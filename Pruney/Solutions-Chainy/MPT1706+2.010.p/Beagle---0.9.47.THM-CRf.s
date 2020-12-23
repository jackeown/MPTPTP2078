%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:26 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   56 (  92 expanded)
%              Number of leaves         :   24 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :   92 ( 285 expanded)
%              Number of equality atoms :    1 (  12 expanded)
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

tff(f_93,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_tmap_1)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_56,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_14,plain,(
    ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_16,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_28,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_24,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_35,plain,(
    ! [B_43,A_44] :
      ( l1_pre_topc(B_43)
      | ~ m1_pre_topc(B_43,A_44)
      | ~ l1_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_38,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_35])).

tff(c_47,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_38])).

tff(c_6,plain,(
    ! [A_6] :
      ( l1_struct_0(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_26,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_56,plain,(
    ! [B_50,A_51] :
      ( m1_subset_1(u1_struct_0(B_50),k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ m1_pre_topc(B_50,A_51)
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( m1_subset_1(A_3,C_5)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(C_5))
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_60,plain,(
    ! [A_52,A_53,B_54] :
      ( m1_subset_1(A_52,u1_struct_0(A_53))
      | ~ r2_hidden(A_52,u1_struct_0(B_54))
      | ~ m1_pre_topc(B_54,A_53)
      | ~ l1_pre_topc(A_53) ) ),
    inference(resolution,[status(thm)],[c_56,c_4])).

tff(c_65,plain,(
    ! [A_55,A_56,B_57] :
      ( m1_subset_1(A_55,u1_struct_0(A_56))
      | ~ m1_pre_topc(B_57,A_56)
      | ~ l1_pre_topc(A_56)
      | v1_xboole_0(u1_struct_0(B_57))
      | ~ m1_subset_1(A_55,u1_struct_0(B_57)) ) ),
    inference(resolution,[status(thm)],[c_2,c_60])).

tff(c_67,plain,(
    ! [A_55] :
      ( m1_subset_1(A_55,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ m1_subset_1(A_55,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_24,c_65])).

tff(c_74,plain,(
    ! [A_55] :
      ( m1_subset_1(A_55,u1_struct_0('#skF_1'))
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ m1_subset_1(A_55,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_67])).

tff(c_81,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_10,plain,(
    ! [A_10] :
      ( ~ v1_xboole_0(u1_struct_0(A_10))
      | ~ l1_struct_0(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_84,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_81,c_10])).

tff(c_87,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_84])).

tff(c_90,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_87])).

tff(c_94,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_90])).

tff(c_96,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_20,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_41,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_35])).

tff(c_50,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_41])).

tff(c_18,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_71,plain,(
    ! [A_55] :
      ( m1_subset_1(A_55,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ m1_subset_1(A_55,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_18,c_65])).

tff(c_80,plain,(
    ! [A_55] :
      ( m1_subset_1(A_55,u1_struct_0('#skF_3'))
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ m1_subset_1(A_55,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_71])).

tff(c_120,plain,(
    ! [A_60] :
      ( m1_subset_1(A_60,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(A_60,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_80])).

tff(c_123,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_16,c_120])).

tff(c_127,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_123])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:21:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.84/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.18  
% 1.84/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.18  %$ r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.84/1.18  
% 1.84/1.18  %Foreground sorts:
% 1.84/1.18  
% 1.84/1.18  
% 1.84/1.18  %Background operators:
% 1.84/1.18  
% 1.84/1.18  
% 1.84/1.18  %Foreground operators:
% 1.84/1.18  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.84/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.84/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.84/1.18  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.84/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.84/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.84/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.84/1.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.84/1.18  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.84/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.84/1.18  tff('#skF_4', type, '#skF_4': $i).
% 1.84/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.84/1.18  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 1.84/1.18  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.84/1.18  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.84/1.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.84/1.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.84/1.18  
% 1.84/1.19  tff(f_93, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (m1_pre_topc(B, C) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (?[E]: (m1_subset_1(E, u1_struct_0(C)) & (E = D)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_tmap_1)).
% 1.84/1.19  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 1.84/1.19  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 1.84/1.19  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 1.84/1.19  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 1.84/1.19  tff(f_37, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 1.84/1.19  tff(f_56, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 1.84/1.19  tff(c_14, plain, (~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 1.84/1.19  tff(c_16, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 1.84/1.19  tff(c_28, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 1.84/1.19  tff(c_24, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 1.84/1.19  tff(c_35, plain, (![B_43, A_44]: (l1_pre_topc(B_43) | ~m1_pre_topc(B_43, A_44) | ~l1_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.84/1.19  tff(c_38, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_35])).
% 1.84/1.19  tff(c_47, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_38])).
% 1.84/1.19  tff(c_6, plain, (![A_6]: (l1_struct_0(A_6) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.84/1.19  tff(c_26, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 1.84/1.19  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.84/1.19  tff(c_56, plain, (![B_50, A_51]: (m1_subset_1(u1_struct_0(B_50), k1_zfmisc_1(u1_struct_0(A_51))) | ~m1_pre_topc(B_50, A_51) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.84/1.19  tff(c_4, plain, (![A_3, C_5, B_4]: (m1_subset_1(A_3, C_5) | ~m1_subset_1(B_4, k1_zfmisc_1(C_5)) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.84/1.19  tff(c_60, plain, (![A_52, A_53, B_54]: (m1_subset_1(A_52, u1_struct_0(A_53)) | ~r2_hidden(A_52, u1_struct_0(B_54)) | ~m1_pre_topc(B_54, A_53) | ~l1_pre_topc(A_53))), inference(resolution, [status(thm)], [c_56, c_4])).
% 1.84/1.19  tff(c_65, plain, (![A_55, A_56, B_57]: (m1_subset_1(A_55, u1_struct_0(A_56)) | ~m1_pre_topc(B_57, A_56) | ~l1_pre_topc(A_56) | v1_xboole_0(u1_struct_0(B_57)) | ~m1_subset_1(A_55, u1_struct_0(B_57)))), inference(resolution, [status(thm)], [c_2, c_60])).
% 1.84/1.19  tff(c_67, plain, (![A_55]: (m1_subset_1(A_55, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | v1_xboole_0(u1_struct_0('#skF_2')) | ~m1_subset_1(A_55, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_24, c_65])).
% 1.84/1.19  tff(c_74, plain, (![A_55]: (m1_subset_1(A_55, u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_2')) | ~m1_subset_1(A_55, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_67])).
% 1.84/1.19  tff(c_81, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_74])).
% 1.84/1.19  tff(c_10, plain, (![A_10]: (~v1_xboole_0(u1_struct_0(A_10)) | ~l1_struct_0(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.84/1.19  tff(c_84, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_81, c_10])).
% 1.84/1.19  tff(c_87, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_26, c_84])).
% 1.84/1.19  tff(c_90, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_6, c_87])).
% 1.84/1.19  tff(c_94, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_47, c_90])).
% 1.84/1.19  tff(c_96, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_74])).
% 1.84/1.19  tff(c_20, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 1.84/1.19  tff(c_41, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_35])).
% 1.84/1.19  tff(c_50, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_41])).
% 1.84/1.19  tff(c_18, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 1.84/1.19  tff(c_71, plain, (![A_55]: (m1_subset_1(A_55, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | v1_xboole_0(u1_struct_0('#skF_2')) | ~m1_subset_1(A_55, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_18, c_65])).
% 1.84/1.19  tff(c_80, plain, (![A_55]: (m1_subset_1(A_55, u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_2')) | ~m1_subset_1(A_55, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_71])).
% 1.84/1.19  tff(c_120, plain, (![A_60]: (m1_subset_1(A_60, u1_struct_0('#skF_3')) | ~m1_subset_1(A_60, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_96, c_80])).
% 1.84/1.19  tff(c_123, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_16, c_120])).
% 1.84/1.19  tff(c_127, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_123])).
% 1.84/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.19  
% 1.84/1.19  Inference rules
% 1.84/1.19  ----------------------
% 1.84/1.19  #Ref     : 0
% 1.84/1.19  #Sup     : 14
% 1.84/1.19  #Fact    : 0
% 1.84/1.19  #Define  : 0
% 1.84/1.19  #Split   : 2
% 1.84/1.19  #Chain   : 0
% 1.84/1.19  #Close   : 0
% 1.84/1.19  
% 1.84/1.19  Ordering : KBO
% 1.84/1.19  
% 1.84/1.19  Simplification rules
% 1.84/1.19  ----------------------
% 1.84/1.19  #Subsume      : 0
% 1.84/1.19  #Demod        : 9
% 1.84/1.19  #Tautology    : 1
% 1.84/1.19  #SimpNegUnit  : 4
% 1.84/1.19  #BackRed      : 0
% 1.84/1.19  
% 1.84/1.19  #Partial instantiations: 0
% 1.84/1.19  #Strategies tried      : 1
% 1.84/1.19  
% 1.84/1.19  Timing (in seconds)
% 1.84/1.19  ----------------------
% 1.84/1.19  Preprocessing        : 0.28
% 1.84/1.19  Parsing              : 0.16
% 1.84/1.19  CNF conversion       : 0.02
% 1.84/1.19  Main loop            : 0.15
% 1.84/1.19  Inferencing          : 0.06
% 1.84/1.19  Reduction            : 0.04
% 1.84/1.19  Demodulation         : 0.03
% 1.84/1.19  BG Simplification    : 0.01
% 1.84/1.19  Subsumption          : 0.02
% 1.84/1.19  Abstraction          : 0.01
% 1.84/1.19  MUC search           : 0.00
% 1.84/1.19  Cooper               : 0.00
% 1.84/1.19  Total                : 0.46
% 1.84/1.19  Index Insertion      : 0.00
% 1.84/1.19  Index Deletion       : 0.00
% 1.84/1.19  Index Matching       : 0.00
% 1.84/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
