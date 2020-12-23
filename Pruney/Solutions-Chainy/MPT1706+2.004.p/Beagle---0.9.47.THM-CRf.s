%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:25 EST 2020

% Result     : Theorem 2.57s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 107 expanded)
%              Number of leaves         :   24 (  47 expanded)
%              Depth                    :    9
%              Number of atoms          :  114 ( 340 expanded)
%              Number of equality atoms :    1 (  15 expanded)
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

tff(f_101,negated_conjecture,(
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

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_49,axiom,(
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

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_64,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_30,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_40,plain,(
    ! [B_43,A_44] :
      ( l1_pre_topc(B_43)
      | ~ m1_pre_topc(B_43,A_44)
      | ~ l1_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_43,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_40])).

tff(c_52,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_43])).

tff(c_12,plain,(
    ! [A_7] :
      ( l1_struct_0(A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_26,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_46,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_40])).

tff(c_55,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_46])).

tff(c_28,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_66,plain,(
    ! [B_48,A_49] :
      ( m1_subset_1(B_48,A_49)
      | ~ v1_xboole_0(B_48)
      | ~ v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_20,plain,(
    ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_74,plain,
    ( ~ v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_66,c_20])).

tff(c_75,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_24,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_22,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_59,plain,(
    ! [B_45,A_46] :
      ( v1_xboole_0(B_45)
      | ~ m1_subset_1(B_45,A_46)
      | ~ v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_63,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_22,c_59])).

tff(c_64,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_63])).

tff(c_18,plain,(
    ! [B_14,A_12] :
      ( m1_subset_1(u1_struct_0(B_14),k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ m1_pre_topc(B_14,A_12)
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r2_hidden(B_2,A_1)
      | ~ m1_subset_1(B_2,A_1)
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_82,plain,(
    ! [C_54,A_55,B_56] :
      ( r2_hidden(C_54,A_55)
      | ~ r2_hidden(C_54,B_56)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_91,plain,(
    ! [B_59,A_60,A_61] :
      ( r2_hidden(B_59,A_60)
      | ~ m1_subset_1(A_61,k1_zfmisc_1(A_60))
      | ~ m1_subset_1(B_59,A_61)
      | v1_xboole_0(A_61) ) ),
    inference(resolution,[status(thm)],[c_4,c_82])).

tff(c_100,plain,(
    ! [B_64,A_65,B_66] :
      ( r2_hidden(B_64,u1_struct_0(A_65))
      | ~ m1_subset_1(B_64,u1_struct_0(B_66))
      | v1_xboole_0(u1_struct_0(B_66))
      | ~ m1_pre_topc(B_66,A_65)
      | ~ l1_pre_topc(A_65) ) ),
    inference(resolution,[status(thm)],[c_18,c_91])).

tff(c_105,plain,(
    ! [A_65] :
      ( r2_hidden('#skF_4',u1_struct_0(A_65))
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ m1_pre_topc('#skF_2',A_65)
      | ~ l1_pre_topc(A_65) ) ),
    inference(resolution,[status(thm)],[c_22,c_100])).

tff(c_110,plain,(
    ! [A_67] :
      ( r2_hidden('#skF_4',u1_struct_0(A_67))
      | ~ m1_pre_topc('#skF_2',A_67)
      | ~ l1_pre_topc(A_67) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_105])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( m1_subset_1(B_2,A_1)
      | ~ r2_hidden(B_2,A_1)
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_118,plain,(
    ! [A_68] :
      ( m1_subset_1('#skF_4',u1_struct_0(A_68))
      | v1_xboole_0(u1_struct_0(A_68))
      | ~ m1_pre_topc('#skF_2',A_68)
      | ~ l1_pre_topc(A_68) ) ),
    inference(resolution,[status(thm)],[c_110,c_2])).

tff(c_126,plain,
    ( v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_118,c_20])).

tff(c_131,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_24,c_126])).

tff(c_133,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_131])).

tff(c_135,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_16,plain,(
    ! [A_11] :
      ( ~ v1_xboole_0(u1_struct_0(A_11))
      | ~ l1_struct_0(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_138,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_135,c_16])).

tff(c_141,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_138])).

tff(c_144,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_141])).

tff(c_148,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_144])).

tff(c_150,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_63])).

tff(c_154,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_150,c_16])).

tff(c_157,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_154])).

tff(c_160,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_157])).

tff(c_164,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_160])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:36:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.57/1.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.55  
% 2.57/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.55  %$ r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.60/1.55  
% 2.60/1.55  %Foreground sorts:
% 2.60/1.55  
% 2.60/1.55  
% 2.60/1.55  %Background operators:
% 2.60/1.55  
% 2.60/1.55  
% 2.60/1.55  %Foreground operators:
% 2.60/1.55  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.60/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.60/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.60/1.55  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.60/1.55  tff('#skF_2', type, '#skF_2': $i).
% 2.60/1.55  tff('#skF_3', type, '#skF_3': $i).
% 2.60/1.55  tff('#skF_1', type, '#skF_1': $i).
% 2.60/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.60/1.55  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.60/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.60/1.55  tff('#skF_4', type, '#skF_4': $i).
% 2.60/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.60/1.55  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.60/1.55  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.60/1.55  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.60/1.55  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.60/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.60/1.55  
% 2.60/1.57  tff(f_101, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (m1_pre_topc(B, C) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (?[E]: (m1_subset_1(E, u1_struct_0(C)) & (E = D)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_tmap_1)).
% 2.60/1.57  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.60/1.57  tff(f_49, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.60/1.57  tff(f_38, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.60/1.57  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 2.60/1.57  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.60/1.57  tff(f_64, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.60/1.57  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.60/1.57  tff(c_30, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.60/1.57  tff(c_40, plain, (![B_43, A_44]: (l1_pre_topc(B_43) | ~m1_pre_topc(B_43, A_44) | ~l1_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.60/1.57  tff(c_43, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_40])).
% 2.60/1.57  tff(c_52, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_43])).
% 2.60/1.57  tff(c_12, plain, (![A_7]: (l1_struct_0(A_7) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.60/1.57  tff(c_32, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.60/1.57  tff(c_26, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.60/1.57  tff(c_46, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_40])).
% 2.60/1.57  tff(c_55, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_46])).
% 2.60/1.57  tff(c_28, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.60/1.57  tff(c_66, plain, (![B_48, A_49]: (m1_subset_1(B_48, A_49) | ~v1_xboole_0(B_48) | ~v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.60/1.57  tff(c_20, plain, (~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.60/1.57  tff(c_74, plain, (~v1_xboole_0('#skF_4') | ~v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_66, c_20])).
% 2.60/1.57  tff(c_75, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_74])).
% 2.60/1.57  tff(c_24, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.60/1.57  tff(c_22, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.60/1.57  tff(c_59, plain, (![B_45, A_46]: (v1_xboole_0(B_45) | ~m1_subset_1(B_45, A_46) | ~v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.60/1.57  tff(c_63, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_22, c_59])).
% 2.60/1.57  tff(c_64, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_63])).
% 2.60/1.57  tff(c_18, plain, (![B_14, A_12]: (m1_subset_1(u1_struct_0(B_14), k1_zfmisc_1(u1_struct_0(A_12))) | ~m1_pre_topc(B_14, A_12) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.60/1.57  tff(c_4, plain, (![B_2, A_1]: (r2_hidden(B_2, A_1) | ~m1_subset_1(B_2, A_1) | v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.60/1.57  tff(c_82, plain, (![C_54, A_55, B_56]: (r2_hidden(C_54, A_55) | ~r2_hidden(C_54, B_56) | ~m1_subset_1(B_56, k1_zfmisc_1(A_55)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.60/1.57  tff(c_91, plain, (![B_59, A_60, A_61]: (r2_hidden(B_59, A_60) | ~m1_subset_1(A_61, k1_zfmisc_1(A_60)) | ~m1_subset_1(B_59, A_61) | v1_xboole_0(A_61))), inference(resolution, [status(thm)], [c_4, c_82])).
% 2.60/1.57  tff(c_100, plain, (![B_64, A_65, B_66]: (r2_hidden(B_64, u1_struct_0(A_65)) | ~m1_subset_1(B_64, u1_struct_0(B_66)) | v1_xboole_0(u1_struct_0(B_66)) | ~m1_pre_topc(B_66, A_65) | ~l1_pre_topc(A_65))), inference(resolution, [status(thm)], [c_18, c_91])).
% 2.60/1.57  tff(c_105, plain, (![A_65]: (r2_hidden('#skF_4', u1_struct_0(A_65)) | v1_xboole_0(u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_2', A_65) | ~l1_pre_topc(A_65))), inference(resolution, [status(thm)], [c_22, c_100])).
% 2.60/1.57  tff(c_110, plain, (![A_67]: (r2_hidden('#skF_4', u1_struct_0(A_67)) | ~m1_pre_topc('#skF_2', A_67) | ~l1_pre_topc(A_67))), inference(negUnitSimplification, [status(thm)], [c_64, c_105])).
% 2.60/1.57  tff(c_2, plain, (![B_2, A_1]: (m1_subset_1(B_2, A_1) | ~r2_hidden(B_2, A_1) | v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.60/1.57  tff(c_118, plain, (![A_68]: (m1_subset_1('#skF_4', u1_struct_0(A_68)) | v1_xboole_0(u1_struct_0(A_68)) | ~m1_pre_topc('#skF_2', A_68) | ~l1_pre_topc(A_68))), inference(resolution, [status(thm)], [c_110, c_2])).
% 2.60/1.57  tff(c_126, plain, (v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_118, c_20])).
% 2.60/1.57  tff(c_131, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_24, c_126])).
% 2.60/1.57  tff(c_133, plain, $false, inference(negUnitSimplification, [status(thm)], [c_75, c_131])).
% 2.60/1.57  tff(c_135, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_74])).
% 2.60/1.57  tff(c_16, plain, (![A_11]: (~v1_xboole_0(u1_struct_0(A_11)) | ~l1_struct_0(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.60/1.57  tff(c_138, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_135, c_16])).
% 2.60/1.57  tff(c_141, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_28, c_138])).
% 2.60/1.57  tff(c_144, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_12, c_141])).
% 2.60/1.57  tff(c_148, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_55, c_144])).
% 2.60/1.57  tff(c_150, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_63])).
% 2.60/1.57  tff(c_154, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_150, c_16])).
% 2.60/1.57  tff(c_157, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_32, c_154])).
% 2.60/1.57  tff(c_160, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_12, c_157])).
% 2.60/1.57  tff(c_164, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_160])).
% 2.60/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.57  
% 2.60/1.58  Inference rules
% 2.60/1.58  ----------------------
% 2.60/1.58  #Ref     : 0
% 2.60/1.58  #Sup     : 22
% 2.60/1.58  #Fact    : 0
% 2.60/1.58  #Define  : 0
% 2.60/1.58  #Split   : 2
% 2.60/1.58  #Chain   : 0
% 2.60/1.58  #Close   : 0
% 2.60/1.58  
% 2.60/1.58  Ordering : KBO
% 2.60/1.58  
% 2.60/1.58  Simplification rules
% 2.60/1.58  ----------------------
% 2.60/1.58  #Subsume      : 0
% 2.60/1.58  #Demod        : 8
% 2.60/1.58  #Tautology    : 6
% 2.60/1.58  #SimpNegUnit  : 4
% 2.60/1.58  #BackRed      : 0
% 2.60/1.58  
% 2.60/1.58  #Partial instantiations: 0
% 2.60/1.58  #Strategies tried      : 1
% 2.60/1.58  
% 2.60/1.58  Timing (in seconds)
% 2.60/1.58  ----------------------
% 2.60/1.58  Preprocessing        : 0.48
% 2.60/1.58  Parsing              : 0.26
% 2.60/1.58  CNF conversion       : 0.04
% 2.60/1.58  Main loop            : 0.29
% 2.60/1.58  Inferencing          : 0.12
% 2.60/1.58  Reduction            : 0.08
% 2.60/1.58  Demodulation         : 0.05
% 2.60/1.58  BG Simplification    : 0.02
% 2.60/1.58  Subsumption          : 0.05
% 2.60/1.58  Abstraction          : 0.01
% 2.60/1.58  MUC search           : 0.00
% 2.60/1.58  Cooper               : 0.00
% 2.60/1.58  Total                : 0.83
% 2.60/1.58  Index Insertion      : 0.00
% 2.60/1.58  Index Deletion       : 0.00
% 2.60/1.58  Index Matching       : 0.00
% 2.60/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
