%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:25 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   56 (  74 expanded)
%              Number of leaves         :   24 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :   93 ( 218 expanded)
%              Number of equality atoms :    1 (  10 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_100,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ( m1_pre_topc(B,C)
                 => ! [D] :
                      ( m1_subset_1(D,u1_struct_0(B))
                     => ? [E] :
                          ( m1_subset_1(E,u1_struct_0(C))
                          & E = D ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_tmap_1)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_63,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_30,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_40,plain,(
    ! [B_42,A_43] :
      ( l1_pre_topc(B_42)
      | ~ m1_pre_topc(B_42,A_43)
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_43,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_40])).

tff(c_52,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_43])).

tff(c_12,plain,(
    ! [A_6] :
      ( l1_struct_0(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_20,plain,(
    ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_22,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_59,plain,(
    ! [B_44,A_45] :
      ( v1_xboole_0(B_44)
      | ~ m1_subset_1(B_44,A_45)
      | ~ v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_63,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_22,c_59])).

tff(c_64,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_63])).

tff(c_26,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_46,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_40])).

tff(c_55,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_46])).

tff(c_24,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r2_hidden(B_2,A_1)
      | ~ m1_subset_1(B_2,A_1)
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_87,plain,(
    ! [B_56,A_57] :
      ( m1_subset_1(u1_struct_0(B_56),k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ m1_pre_topc(B_56,A_57)
      | ~ l1_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_10,plain,(
    ! [A_3,C_5,B_4] :
      ( m1_subset_1(A_3,C_5)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(C_5))
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_100,plain,(
    ! [A_63,A_64,B_65] :
      ( m1_subset_1(A_63,u1_struct_0(A_64))
      | ~ r2_hidden(A_63,u1_struct_0(B_65))
      | ~ m1_pre_topc(B_65,A_64)
      | ~ l1_pre_topc(A_64) ) ),
    inference(resolution,[status(thm)],[c_87,c_10])).

tff(c_105,plain,(
    ! [B_66,A_67,B_68] :
      ( m1_subset_1(B_66,u1_struct_0(A_67))
      | ~ m1_pre_topc(B_68,A_67)
      | ~ l1_pre_topc(A_67)
      | ~ m1_subset_1(B_66,u1_struct_0(B_68))
      | v1_xboole_0(u1_struct_0(B_68)) ) ),
    inference(resolution,[status(thm)],[c_4,c_100])).

tff(c_111,plain,(
    ! [B_66] :
      ( m1_subset_1(B_66,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ m1_subset_1(B_66,u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_24,c_105])).

tff(c_122,plain,(
    ! [B_66] :
      ( m1_subset_1(B_66,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_66,u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_111])).

tff(c_139,plain,(
    ! [B_70] :
      ( m1_subset_1(B_70,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_70,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_122])).

tff(c_146,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_22,c_139])).

tff(c_151,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_146])).

tff(c_153,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_63])).

tff(c_16,plain,(
    ! [A_10] :
      ( ~ v1_xboole_0(u1_struct_0(A_10))
      | ~ l1_struct_0(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_157,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_153,c_16])).

tff(c_160,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_157])).

tff(c_163,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_160])).

tff(c_167,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_163])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:03:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.21  
% 2.04/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.21  %$ r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.04/1.21  
% 2.04/1.21  %Foreground sorts:
% 2.04/1.21  
% 2.04/1.21  
% 2.04/1.21  %Background operators:
% 2.04/1.21  
% 2.04/1.21  
% 2.04/1.21  %Foreground operators:
% 2.04/1.21  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.04/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.04/1.21  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.04/1.21  tff('#skF_2', type, '#skF_2': $i).
% 2.04/1.21  tff('#skF_3', type, '#skF_3': $i).
% 2.04/1.21  tff('#skF_1', type, '#skF_1': $i).
% 2.04/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.04/1.21  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.04/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.21  tff('#skF_4', type, '#skF_4': $i).
% 2.04/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.21  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.04/1.21  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.04/1.21  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.04/1.21  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.04/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.04/1.21  
% 2.04/1.22  tff(f_100, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (m1_pre_topc(B, C) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (?[E]: (m1_subset_1(E, u1_struct_0(C)) & (E = D)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_tmap_1)).
% 2.04/1.22  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.04/1.22  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.04/1.22  tff(f_38, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.04/1.22  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 2.04/1.22  tff(f_44, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.04/1.22  tff(f_63, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.04/1.22  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.04/1.22  tff(c_30, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.04/1.22  tff(c_40, plain, (![B_42, A_43]: (l1_pre_topc(B_42) | ~m1_pre_topc(B_42, A_43) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.04/1.22  tff(c_43, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_40])).
% 2.04/1.22  tff(c_52, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_43])).
% 2.04/1.22  tff(c_12, plain, (![A_6]: (l1_struct_0(A_6) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.04/1.22  tff(c_32, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.04/1.22  tff(c_20, plain, (~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.04/1.22  tff(c_22, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.04/1.22  tff(c_59, plain, (![B_44, A_45]: (v1_xboole_0(B_44) | ~m1_subset_1(B_44, A_45) | ~v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.04/1.22  tff(c_63, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_22, c_59])).
% 2.04/1.22  tff(c_64, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_63])).
% 2.04/1.22  tff(c_26, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.04/1.22  tff(c_46, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_40])).
% 2.04/1.22  tff(c_55, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_46])).
% 2.04/1.22  tff(c_24, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.04/1.22  tff(c_4, plain, (![B_2, A_1]: (r2_hidden(B_2, A_1) | ~m1_subset_1(B_2, A_1) | v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.04/1.22  tff(c_87, plain, (![B_56, A_57]: (m1_subset_1(u1_struct_0(B_56), k1_zfmisc_1(u1_struct_0(A_57))) | ~m1_pre_topc(B_56, A_57) | ~l1_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.04/1.22  tff(c_10, plain, (![A_3, C_5, B_4]: (m1_subset_1(A_3, C_5) | ~m1_subset_1(B_4, k1_zfmisc_1(C_5)) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.04/1.22  tff(c_100, plain, (![A_63, A_64, B_65]: (m1_subset_1(A_63, u1_struct_0(A_64)) | ~r2_hidden(A_63, u1_struct_0(B_65)) | ~m1_pre_topc(B_65, A_64) | ~l1_pre_topc(A_64))), inference(resolution, [status(thm)], [c_87, c_10])).
% 2.04/1.22  tff(c_105, plain, (![B_66, A_67, B_68]: (m1_subset_1(B_66, u1_struct_0(A_67)) | ~m1_pre_topc(B_68, A_67) | ~l1_pre_topc(A_67) | ~m1_subset_1(B_66, u1_struct_0(B_68)) | v1_xboole_0(u1_struct_0(B_68)))), inference(resolution, [status(thm)], [c_4, c_100])).
% 2.04/1.22  tff(c_111, plain, (![B_66]: (m1_subset_1(B_66, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~m1_subset_1(B_66, u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_24, c_105])).
% 2.04/1.22  tff(c_122, plain, (![B_66]: (m1_subset_1(B_66, u1_struct_0('#skF_3')) | ~m1_subset_1(B_66, u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_111])).
% 2.04/1.22  tff(c_139, plain, (![B_70]: (m1_subset_1(B_70, u1_struct_0('#skF_3')) | ~m1_subset_1(B_70, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_64, c_122])).
% 2.04/1.22  tff(c_146, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_22, c_139])).
% 2.04/1.22  tff(c_151, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_146])).
% 2.04/1.22  tff(c_153, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_63])).
% 2.04/1.22  tff(c_16, plain, (![A_10]: (~v1_xboole_0(u1_struct_0(A_10)) | ~l1_struct_0(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.04/1.22  tff(c_157, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_153, c_16])).
% 2.04/1.22  tff(c_160, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_32, c_157])).
% 2.04/1.22  tff(c_163, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_12, c_160])).
% 2.04/1.22  tff(c_167, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_163])).
% 2.04/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.22  
% 2.04/1.22  Inference rules
% 2.04/1.22  ----------------------
% 2.04/1.22  #Ref     : 0
% 2.04/1.22  #Sup     : 22
% 2.04/1.22  #Fact    : 0
% 2.04/1.22  #Define  : 0
% 2.04/1.22  #Split   : 3
% 2.04/1.22  #Chain   : 0
% 2.04/1.22  #Close   : 0
% 2.04/1.22  
% 2.04/1.22  Ordering : KBO
% 2.04/1.22  
% 2.04/1.22  Simplification rules
% 2.04/1.22  ----------------------
% 2.04/1.22  #Subsume      : 2
% 2.04/1.22  #Demod        : 8
% 2.04/1.22  #Tautology    : 4
% 2.04/1.22  #SimpNegUnit  : 5
% 2.04/1.22  #BackRed      : 0
% 2.04/1.22  
% 2.04/1.22  #Partial instantiations: 0
% 2.04/1.22  #Strategies tried      : 1
% 2.04/1.22  
% 2.04/1.22  Timing (in seconds)
% 2.04/1.22  ----------------------
% 2.04/1.23  Preprocessing        : 0.28
% 2.04/1.23  Parsing              : 0.16
% 2.04/1.23  CNF conversion       : 0.02
% 2.04/1.23  Main loop            : 0.17
% 2.04/1.23  Inferencing          : 0.07
% 2.04/1.23  Reduction            : 0.04
% 2.04/1.23  Demodulation         : 0.03
% 2.04/1.23  BG Simplification    : 0.01
% 2.04/1.23  Subsumption          : 0.03
% 2.04/1.23  Abstraction          : 0.01
% 2.04/1.23  MUC search           : 0.00
% 2.04/1.23  Cooper               : 0.00
% 2.04/1.23  Total                : 0.49
% 2.04/1.23  Index Insertion      : 0.00
% 2.04/1.23  Index Deletion       : 0.00
% 2.04/1.23  Index Matching       : 0.00
% 2.04/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
