%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:37 EST 2020

% Result     : Theorem 4.87s
% Output     : CNFRefutation 4.87s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 157 expanded)
%              Number of leaves         :   34 (  70 expanded)
%              Depth                    :    9
%              Number of atoms          :  140 ( 377 expanded)
%              Number of equality atoms :   15 (  43 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_46,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_109,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tex_2(B,A)
             => ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ( r2_hidden(C,B)
                   => k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,k6_domain_1(u1_struct_0(A),C))) = k6_domain_1(u1_struct_0(A),C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_tex_2)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_89,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r1_tarski(C,B)
                 => k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,C)) = C ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tex_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(c_100,plain,(
    ! [A_52,B_53] :
      ( r2_hidden('#skF_2'(A_52,B_53),A_52)
      | r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_108,plain,(
    ! [A_52] : r1_tarski(A_52,A_52) ),
    inference(resolution,[status(thm)],[c_100,c_8])).

tff(c_14,plain,(
    ! [A_13] : k2_tarski(A_13,A_13) = k1_tarski(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_120,plain,(
    ! [A_57,C_58,B_59] :
      ( r2_hidden(A_57,C_58)
      | ~ r1_tarski(k2_tarski(A_57,B_59),C_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_134,plain,(
    ! [A_60,B_61] : r2_hidden(A_60,k2_tarski(A_60,B_61)) ),
    inference(resolution,[status(thm)],[c_108,c_120])).

tff(c_140,plain,(
    ! [A_13] : r2_hidden(A_13,k1_tarski(A_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_134])).

tff(c_40,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_392,plain,(
    ! [A_99,B_100,C_101] :
      ( r1_tarski(k2_tarski(A_99,B_100),C_101)
      | ~ r2_hidden(B_100,C_101)
      | ~ r2_hidden(A_99,C_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_418,plain,(
    ! [A_13,C_101] :
      ( r1_tarski(k1_tarski(A_13),C_101)
      | ~ r2_hidden(A_13,C_101)
      | ~ r2_hidden(A_13,C_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_392])).

tff(c_429,plain,(
    ! [A_102,C_103] :
      ( r1_tarski(k1_tarski(A_102),C_103)
      | ~ r2_hidden(A_102,C_103)
      | ~ r2_hidden(A_102,C_103) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_392])).

tff(c_12,plain,(
    ! [A_10,C_12,B_11] :
      ( r1_tarski(A_10,C_12)
      | ~ r1_tarski(B_11,C_12)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_451,plain,(
    ! [A_104,C_105,A_106] :
      ( r1_tarski(A_104,C_105)
      | ~ r1_tarski(A_104,k1_tarski(A_106))
      | ~ r2_hidden(A_106,C_105) ) ),
    inference(resolution,[status(thm)],[c_429,c_12])).

tff(c_581,plain,(
    ! [A_122,C_123,A_124] :
      ( r1_tarski(k1_tarski(A_122),C_123)
      | ~ r2_hidden(A_124,C_123)
      | ~ r2_hidden(A_122,k1_tarski(A_124)) ) ),
    inference(resolution,[status(thm)],[c_418,c_451])).

tff(c_618,plain,(
    ! [A_125] :
      ( r1_tarski(k1_tarski(A_125),'#skF_5')
      | ~ r2_hidden(A_125,k1_tarski('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_40,c_581])).

tff(c_646,plain,(
    r1_tarski(k1_tarski('#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_140,c_618])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_72,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(A_42,B_43)
      | ~ m1_subset_1(A_42,k1_zfmisc_1(B_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_76,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_46,c_72])).

tff(c_174,plain,(
    ! [A_71,C_72,B_73] :
      ( r1_tarski(A_71,C_72)
      | ~ r1_tarski(B_73,C_72)
      | ~ r1_tarski(A_71,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_196,plain,(
    ! [A_76] :
      ( r1_tarski(A_76,u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_76,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_76,c_174])).

tff(c_215,plain,(
    ! [A_10,A_76] :
      ( r1_tarski(A_10,u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_10,A_76)
      | ~ r1_tarski(A_76,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_196,c_12])).

tff(c_652,plain,
    ( r1_tarski(k1_tarski('#skF_6'),u1_struct_0('#skF_4'))
    | ~ r1_tarski('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_646,c_215])).

tff(c_667,plain,(
    r1_tarski(k1_tarski('#skF_6'),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_652])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_50,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_48,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_44,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_26,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(A_20,k1_zfmisc_1(B_21))
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_959,plain,(
    ! [A_136,B_137,C_138] :
      ( k9_subset_1(u1_struct_0(A_136),B_137,k2_pre_topc(A_136,C_138)) = C_138
      | ~ r1_tarski(C_138,B_137)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(u1_struct_0(A_136)))
      | ~ v2_tex_2(B_137,A_136)
      | ~ m1_subset_1(B_137,k1_zfmisc_1(u1_struct_0(A_136)))
      | ~ l1_pre_topc(A_136)
      | ~ v2_pre_topc(A_136)
      | v2_struct_0(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2834,plain,(
    ! [A_236,B_237,A_238] :
      ( k9_subset_1(u1_struct_0(A_236),B_237,k2_pre_topc(A_236,A_238)) = A_238
      | ~ r1_tarski(A_238,B_237)
      | ~ v2_tex_2(B_237,A_236)
      | ~ m1_subset_1(B_237,k1_zfmisc_1(u1_struct_0(A_236)))
      | ~ l1_pre_topc(A_236)
      | ~ v2_pre_topc(A_236)
      | v2_struct_0(A_236)
      | ~ r1_tarski(A_238,u1_struct_0(A_236)) ) ),
    inference(resolution,[status(thm)],[c_26,c_959])).

tff(c_2841,plain,(
    ! [A_238] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',A_238)) = A_238
      | ~ r1_tarski(A_238,'#skF_5')
      | ~ v2_tex_2('#skF_5','#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_238,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_46,c_2834])).

tff(c_2846,plain,(
    ! [A_238] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',A_238)) = A_238
      | ~ r1_tarski(A_238,'#skF_5')
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_238,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_44,c_2841])).

tff(c_2985,plain,(
    ! [A_241] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',A_241)) = A_241
      | ~ r1_tarski(A_241,'#skF_5')
      | ~ r1_tarski(A_241,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_2846])).

tff(c_53,plain,(
    ! [B_38,A_39] :
      ( ~ r2_hidden(B_38,A_39)
      | ~ v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_57,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_53])).

tff(c_82,plain,(
    ! [B_46,A_47] :
      ( v1_xboole_0(B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_47))
      | ~ v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_88,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_46,c_82])).

tff(c_92,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_88])).

tff(c_42,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_356,plain,(
    ! [A_95,B_96] :
      ( k6_domain_1(A_95,B_96) = k1_tarski(B_96)
      | ~ m1_subset_1(B_96,A_95)
      | v1_xboole_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_365,plain,
    ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_42,c_356])).

tff(c_370,plain,(
    k6_domain_1(u1_struct_0('#skF_4'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_365])).

tff(c_38,plain,(
    k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),'#skF_6'))) != k6_domain_1(u1_struct_0('#skF_4'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_371,plain,(
    k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',k1_tarski('#skF_6'))) != k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_370,c_370,c_38])).

tff(c_3002,plain,
    ( ~ r1_tarski(k1_tarski('#skF_6'),'#skF_5')
    | ~ r1_tarski(k1_tarski('#skF_6'),u1_struct_0('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2985,c_371])).

tff(c_3027,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_667,c_646,c_3002])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:14:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.87/1.94  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.87/1.95  
% 4.87/1.95  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.87/1.95  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 4.87/1.95  
% 4.87/1.95  %Foreground sorts:
% 4.87/1.95  
% 4.87/1.95  
% 4.87/1.95  %Background operators:
% 4.87/1.95  
% 4.87/1.95  
% 4.87/1.95  %Foreground operators:
% 4.87/1.95  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.87/1.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.87/1.95  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.87/1.95  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.87/1.95  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.87/1.95  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.87/1.95  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.87/1.95  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.87/1.95  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.87/1.95  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.87/1.95  tff('#skF_5', type, '#skF_5': $i).
% 4.87/1.95  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.87/1.95  tff('#skF_6', type, '#skF_6': $i).
% 4.87/1.95  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.87/1.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.87/1.95  tff('#skF_4', type, '#skF_4': $i).
% 4.87/1.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.87/1.95  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.87/1.95  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.87/1.95  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.87/1.95  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.87/1.95  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.87/1.95  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.87/1.95  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.87/1.95  
% 4.87/1.97  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.87/1.97  tff(f_46, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.87/1.97  tff(f_52, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 4.87/1.97  tff(f_109, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_tex_2)).
% 4.87/1.97  tff(f_44, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.87/1.97  tff(f_63, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.87/1.97  tff(f_89, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tex_2)).
% 4.87/1.97  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.87/1.97  tff(f_59, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 4.87/1.97  tff(f_70, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 4.87/1.97  tff(c_100, plain, (![A_52, B_53]: (r2_hidden('#skF_2'(A_52, B_53), A_52) | r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.87/1.97  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.87/1.97  tff(c_108, plain, (![A_52]: (r1_tarski(A_52, A_52))), inference(resolution, [status(thm)], [c_100, c_8])).
% 4.87/1.97  tff(c_14, plain, (![A_13]: (k2_tarski(A_13, A_13)=k1_tarski(A_13))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.87/1.97  tff(c_120, plain, (![A_57, C_58, B_59]: (r2_hidden(A_57, C_58) | ~r1_tarski(k2_tarski(A_57, B_59), C_58))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.87/1.97  tff(c_134, plain, (![A_60, B_61]: (r2_hidden(A_60, k2_tarski(A_60, B_61)))), inference(resolution, [status(thm)], [c_108, c_120])).
% 4.87/1.97  tff(c_140, plain, (![A_13]: (r2_hidden(A_13, k1_tarski(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_134])).
% 4.87/1.97  tff(c_40, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.87/1.97  tff(c_392, plain, (![A_99, B_100, C_101]: (r1_tarski(k2_tarski(A_99, B_100), C_101) | ~r2_hidden(B_100, C_101) | ~r2_hidden(A_99, C_101))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.87/1.97  tff(c_418, plain, (![A_13, C_101]: (r1_tarski(k1_tarski(A_13), C_101) | ~r2_hidden(A_13, C_101) | ~r2_hidden(A_13, C_101))), inference(superposition, [status(thm), theory('equality')], [c_14, c_392])).
% 4.87/1.97  tff(c_429, plain, (![A_102, C_103]: (r1_tarski(k1_tarski(A_102), C_103) | ~r2_hidden(A_102, C_103) | ~r2_hidden(A_102, C_103))), inference(superposition, [status(thm), theory('equality')], [c_14, c_392])).
% 4.87/1.97  tff(c_12, plain, (![A_10, C_12, B_11]: (r1_tarski(A_10, C_12) | ~r1_tarski(B_11, C_12) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.87/1.97  tff(c_451, plain, (![A_104, C_105, A_106]: (r1_tarski(A_104, C_105) | ~r1_tarski(A_104, k1_tarski(A_106)) | ~r2_hidden(A_106, C_105))), inference(resolution, [status(thm)], [c_429, c_12])).
% 4.87/1.97  tff(c_581, plain, (![A_122, C_123, A_124]: (r1_tarski(k1_tarski(A_122), C_123) | ~r2_hidden(A_124, C_123) | ~r2_hidden(A_122, k1_tarski(A_124)))), inference(resolution, [status(thm)], [c_418, c_451])).
% 4.87/1.97  tff(c_618, plain, (![A_125]: (r1_tarski(k1_tarski(A_125), '#skF_5') | ~r2_hidden(A_125, k1_tarski('#skF_6')))), inference(resolution, [status(thm)], [c_40, c_581])).
% 4.87/1.97  tff(c_646, plain, (r1_tarski(k1_tarski('#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_140, c_618])).
% 4.87/1.97  tff(c_46, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.87/1.97  tff(c_72, plain, (![A_42, B_43]: (r1_tarski(A_42, B_43) | ~m1_subset_1(A_42, k1_zfmisc_1(B_43)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.87/1.97  tff(c_76, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_46, c_72])).
% 4.87/1.97  tff(c_174, plain, (![A_71, C_72, B_73]: (r1_tarski(A_71, C_72) | ~r1_tarski(B_73, C_72) | ~r1_tarski(A_71, B_73))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.87/1.97  tff(c_196, plain, (![A_76]: (r1_tarski(A_76, u1_struct_0('#skF_4')) | ~r1_tarski(A_76, '#skF_5'))), inference(resolution, [status(thm)], [c_76, c_174])).
% 4.87/1.97  tff(c_215, plain, (![A_10, A_76]: (r1_tarski(A_10, u1_struct_0('#skF_4')) | ~r1_tarski(A_10, A_76) | ~r1_tarski(A_76, '#skF_5'))), inference(resolution, [status(thm)], [c_196, c_12])).
% 4.87/1.97  tff(c_652, plain, (r1_tarski(k1_tarski('#skF_6'), u1_struct_0('#skF_4')) | ~r1_tarski('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_646, c_215])).
% 4.87/1.97  tff(c_667, plain, (r1_tarski(k1_tarski('#skF_6'), u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_652])).
% 4.87/1.97  tff(c_52, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.87/1.97  tff(c_50, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.87/1.97  tff(c_48, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.87/1.97  tff(c_44, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.87/1.97  tff(c_26, plain, (![A_20, B_21]: (m1_subset_1(A_20, k1_zfmisc_1(B_21)) | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.87/1.97  tff(c_959, plain, (![A_136, B_137, C_138]: (k9_subset_1(u1_struct_0(A_136), B_137, k2_pre_topc(A_136, C_138))=C_138 | ~r1_tarski(C_138, B_137) | ~m1_subset_1(C_138, k1_zfmisc_1(u1_struct_0(A_136))) | ~v2_tex_2(B_137, A_136) | ~m1_subset_1(B_137, k1_zfmisc_1(u1_struct_0(A_136))) | ~l1_pre_topc(A_136) | ~v2_pre_topc(A_136) | v2_struct_0(A_136))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.87/1.97  tff(c_2834, plain, (![A_236, B_237, A_238]: (k9_subset_1(u1_struct_0(A_236), B_237, k2_pre_topc(A_236, A_238))=A_238 | ~r1_tarski(A_238, B_237) | ~v2_tex_2(B_237, A_236) | ~m1_subset_1(B_237, k1_zfmisc_1(u1_struct_0(A_236))) | ~l1_pre_topc(A_236) | ~v2_pre_topc(A_236) | v2_struct_0(A_236) | ~r1_tarski(A_238, u1_struct_0(A_236)))), inference(resolution, [status(thm)], [c_26, c_959])).
% 4.87/1.97  tff(c_2841, plain, (![A_238]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', A_238))=A_238 | ~r1_tarski(A_238, '#skF_5') | ~v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~r1_tarski(A_238, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_46, c_2834])).
% 4.87/1.97  tff(c_2846, plain, (![A_238]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', A_238))=A_238 | ~r1_tarski(A_238, '#skF_5') | v2_struct_0('#skF_4') | ~r1_tarski(A_238, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_44, c_2841])).
% 4.87/1.97  tff(c_2985, plain, (![A_241]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', A_241))=A_241 | ~r1_tarski(A_241, '#skF_5') | ~r1_tarski(A_241, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_52, c_2846])).
% 4.87/1.97  tff(c_53, plain, (![B_38, A_39]: (~r2_hidden(B_38, A_39) | ~v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.87/1.97  tff(c_57, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_40, c_53])).
% 4.87/1.97  tff(c_82, plain, (![B_46, A_47]: (v1_xboole_0(B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(A_47)) | ~v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.87/1.97  tff(c_88, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_46, c_82])).
% 4.87/1.97  tff(c_92, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_57, c_88])).
% 4.87/1.97  tff(c_42, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.87/1.97  tff(c_356, plain, (![A_95, B_96]: (k6_domain_1(A_95, B_96)=k1_tarski(B_96) | ~m1_subset_1(B_96, A_95) | v1_xboole_0(A_95))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.87/1.97  tff(c_365, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_42, c_356])).
% 4.87/1.97  tff(c_370, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')=k1_tarski('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_92, c_365])).
% 4.87/1.97  tff(c_38, plain, (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')))!=k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.87/1.97  tff(c_371, plain, (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', k1_tarski('#skF_6')))!=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_370, c_370, c_38])).
% 4.87/1.97  tff(c_3002, plain, (~r1_tarski(k1_tarski('#skF_6'), '#skF_5') | ~r1_tarski(k1_tarski('#skF_6'), u1_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2985, c_371])).
% 4.87/1.97  tff(c_3027, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_667, c_646, c_3002])).
% 4.87/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.87/1.97  
% 4.87/1.97  Inference rules
% 4.87/1.97  ----------------------
% 4.87/1.97  #Ref     : 0
% 4.87/1.97  #Sup     : 692
% 4.87/1.97  #Fact    : 0
% 4.87/1.97  #Define  : 0
% 4.87/1.97  #Split   : 3
% 4.87/1.97  #Chain   : 0
% 4.87/1.97  #Close   : 0
% 4.87/1.97  
% 4.87/1.97  Ordering : KBO
% 4.87/1.97  
% 4.87/1.97  Simplification rules
% 4.87/1.97  ----------------------
% 4.87/1.97  #Subsume      : 217
% 4.87/1.97  #Demod        : 153
% 4.87/1.97  #Tautology    : 145
% 4.87/1.97  #SimpNegUnit  : 82
% 4.87/1.97  #BackRed      : 9
% 4.87/1.97  
% 4.87/1.97  #Partial instantiations: 0
% 4.87/1.97  #Strategies tried      : 1
% 4.87/1.97  
% 4.87/1.97  Timing (in seconds)
% 4.87/1.97  ----------------------
% 4.87/1.97  Preprocessing        : 0.35
% 4.87/1.97  Parsing              : 0.18
% 4.87/1.97  CNF conversion       : 0.03
% 4.87/1.97  Main loop            : 0.80
% 4.87/1.97  Inferencing          : 0.28
% 4.87/1.97  Reduction            : 0.24
% 4.87/1.97  Demodulation         : 0.16
% 4.87/1.97  BG Simplification    : 0.03
% 4.87/1.97  Subsumption          : 0.19
% 4.87/1.97  Abstraction          : 0.04
% 4.87/1.97  MUC search           : 0.00
% 4.87/1.97  Cooper               : 0.00
% 4.87/1.97  Total                : 1.18
% 4.87/1.97  Index Insertion      : 0.00
% 4.87/1.97  Index Deletion       : 0.00
% 4.87/1.97  Index Matching       : 0.00
% 4.87/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
