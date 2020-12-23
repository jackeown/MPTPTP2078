%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:38 EST 2020

% Result     : Theorem 5.34s
% Output     : CNFRefutation 5.83s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 183 expanded)
%              Number of leaves         :   32 (  79 expanded)
%              Depth                    :   10
%              Number of atoms          :  140 ( 518 expanded)
%              Number of equality atoms :   13 (  59 expanded)
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

tff(f_101,negated_conjecture,(
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
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_81,axiom,(
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

tff(f_51,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(c_34,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_87,plain,(
    ! [A_44,B_45] :
      ( m1_subset_1(k1_tarski(A_44),k1_zfmisc_1(B_45))
      | ~ r2_hidden(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_18,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(A_16,B_17)
      | ~ m1_subset_1(A_16,k1_zfmisc_1(B_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_95,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(k1_tarski(A_44),B_45)
      | ~ r2_hidden(A_44,B_45) ) ),
    inference(resolution,[status(thm)],[c_87,c_18])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_66,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(A_38,B_39)
      | ~ m1_subset_1(A_38,k1_zfmisc_1(B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_70,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_40,c_66])).

tff(c_108,plain,(
    ! [A_52,B_53] :
      ( r2_hidden('#skF_2'(A_52,B_53),A_52)
      | r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_116,plain,(
    ! [A_52] : r1_tarski(A_52,A_52) ),
    inference(resolution,[status(thm)],[c_108,c_8])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_128,plain,(
    ! [C_57,B_58,A_59] :
      ( r2_hidden(C_57,B_58)
      | ~ r2_hidden(C_57,A_59)
      | ~ r1_tarski(A_59,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_248,plain,(
    ! [A_73,B_74,B_75] :
      ( r2_hidden('#skF_2'(A_73,B_74),B_75)
      | ~ r1_tarski(A_73,B_75)
      | r1_tarski(A_73,B_74) ) ),
    inference(resolution,[status(thm)],[c_10,c_128])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_393,plain,(
    ! [A_102,B_103,B_104,B_105] :
      ( r2_hidden('#skF_2'(A_102,B_103),B_104)
      | ~ r1_tarski(B_105,B_104)
      | ~ r1_tarski(A_102,B_105)
      | r1_tarski(A_102,B_103) ) ),
    inference(resolution,[status(thm)],[c_248,c_6])).

tff(c_552,plain,(
    ! [A_119,B_120,B_121,A_122] :
      ( r2_hidden('#skF_2'(A_119,B_120),B_121)
      | ~ r1_tarski(A_119,k1_tarski(A_122))
      | r1_tarski(A_119,B_120)
      | ~ r2_hidden(A_122,B_121) ) ),
    inference(resolution,[status(thm)],[c_95,c_393])).

tff(c_565,plain,(
    ! [A_123,B_124,B_125] :
      ( r2_hidden('#skF_2'(k1_tarski(A_123),B_124),B_125)
      | r1_tarski(k1_tarski(A_123),B_124)
      | ~ r2_hidden(A_123,B_125) ) ),
    inference(resolution,[status(thm)],[c_116,c_552])).

tff(c_2457,plain,(
    ! [A_240,B_241,B_242,B_243] :
      ( r2_hidden('#skF_2'(k1_tarski(A_240),B_241),B_242)
      | ~ r1_tarski(B_243,B_242)
      | r1_tarski(k1_tarski(A_240),B_241)
      | ~ r2_hidden(A_240,B_243) ) ),
    inference(resolution,[status(thm)],[c_565,c_6])).

tff(c_2482,plain,(
    ! [A_244,B_245] :
      ( r2_hidden('#skF_2'(k1_tarski(A_244),B_245),u1_struct_0('#skF_4'))
      | r1_tarski(k1_tarski(A_244),B_245)
      | ~ r2_hidden(A_244,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_70,c_2457])).

tff(c_2499,plain,(
    ! [A_244] :
      ( r1_tarski(k1_tarski(A_244),u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_244,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2482,c_8])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_44,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_42,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_38,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_20,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(A_16,k1_zfmisc_1(B_17))
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_458,plain,(
    ! [A_109,B_110,C_111] :
      ( k9_subset_1(u1_struct_0(A_109),B_110,k2_pre_topc(A_109,C_111)) = C_111
      | ~ r1_tarski(C_111,B_110)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ v2_tex_2(B_110,A_109)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ l1_pre_topc(A_109)
      | ~ v2_pre_topc(A_109)
      | v2_struct_0(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2988,plain,(
    ! [A_268,B_269,A_270] :
      ( k9_subset_1(u1_struct_0(A_268),B_269,k2_pre_topc(A_268,A_270)) = A_270
      | ~ r1_tarski(A_270,B_269)
      | ~ v2_tex_2(B_269,A_268)
      | ~ m1_subset_1(B_269,k1_zfmisc_1(u1_struct_0(A_268)))
      | ~ l1_pre_topc(A_268)
      | ~ v2_pre_topc(A_268)
      | v2_struct_0(A_268)
      | ~ r1_tarski(A_270,u1_struct_0(A_268)) ) ),
    inference(resolution,[status(thm)],[c_20,c_458])).

tff(c_2998,plain,(
    ! [A_270] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',A_270)) = A_270
      | ~ r1_tarski(A_270,'#skF_5')
      | ~ v2_tex_2('#skF_5','#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_270,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_40,c_2988])).

tff(c_3004,plain,(
    ! [A_270] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',A_270)) = A_270
      | ~ r1_tarski(A_270,'#skF_5')
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_270,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_38,c_2998])).

tff(c_3073,plain,(
    ! [A_273] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',A_273)) = A_273
      | ~ r1_tarski(A_273,'#skF_5')
      | ~ r1_tarski(A_273,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_3004])).

tff(c_47,plain,(
    ! [B_34,A_35] :
      ( ~ r2_hidden(B_34,A_35)
      | ~ v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_51,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_47])).

tff(c_76,plain,(
    ! [B_42,A_43] :
      ( v1_xboole_0(B_42)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_43))
      | ~ v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_82,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_40,c_76])).

tff(c_86,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_82])).

tff(c_36,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_138,plain,(
    ! [A_60,B_61] :
      ( k6_domain_1(A_60,B_61) = k1_tarski(B_61)
      | ~ m1_subset_1(B_61,A_60)
      | v1_xboole_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_150,plain,
    ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_36,c_138])).

tff(c_156,plain,(
    k6_domain_1(u1_struct_0('#skF_4'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_150])).

tff(c_32,plain,(
    k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),'#skF_6'))) != k6_domain_1(u1_struct_0('#skF_4'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_180,plain,(
    k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',k1_tarski('#skF_6'))) != k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_156,c_32])).

tff(c_3112,plain,
    ( ~ r1_tarski(k1_tarski('#skF_6'),'#skF_5')
    | ~ r1_tarski(k1_tarski('#skF_6'),u1_struct_0('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3073,c_180])).

tff(c_3120,plain,(
    ~ r1_tarski(k1_tarski('#skF_6'),u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_3112])).

tff(c_3123,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_2499,c_3120])).

tff(c_3136,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_3123])).

tff(c_3137,plain,(
    ~ r1_tarski(k1_tarski('#skF_6'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_3112])).

tff(c_3144,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_95,c_3137])).

tff(c_3149,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_3144])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:08:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.34/2.07  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.34/2.08  
% 5.34/2.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.75/2.08  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 5.75/2.08  
% 5.75/2.08  %Foreground sorts:
% 5.75/2.08  
% 5.75/2.08  
% 5.75/2.08  %Background operators:
% 5.75/2.08  
% 5.75/2.08  
% 5.75/2.08  %Foreground operators:
% 5.75/2.08  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.75/2.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.75/2.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.75/2.08  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.75/2.08  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.75/2.08  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.75/2.08  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.75/2.08  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 5.75/2.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.75/2.08  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.75/2.08  tff('#skF_5', type, '#skF_5': $i).
% 5.75/2.08  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 5.75/2.08  tff('#skF_6', type, '#skF_6': $i).
% 5.75/2.08  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.75/2.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.75/2.08  tff('#skF_4', type, '#skF_4': $i).
% 5.75/2.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.75/2.08  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.75/2.08  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.75/2.08  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.75/2.08  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.75/2.08  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.75/2.08  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 5.75/2.08  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.75/2.08  
% 5.75/2.09  tff(f_101, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_tex_2)).
% 5.75/2.09  tff(f_44, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 5.75/2.09  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.75/2.09  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.75/2.09  tff(f_81, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tex_2)).
% 5.75/2.09  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.75/2.09  tff(f_51, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 5.75/2.09  tff(f_62, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 5.75/2.09  tff(c_34, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.75/2.09  tff(c_87, plain, (![A_44, B_45]: (m1_subset_1(k1_tarski(A_44), k1_zfmisc_1(B_45)) | ~r2_hidden(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.75/2.09  tff(c_18, plain, (![A_16, B_17]: (r1_tarski(A_16, B_17) | ~m1_subset_1(A_16, k1_zfmisc_1(B_17)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.75/2.09  tff(c_95, plain, (![A_44, B_45]: (r1_tarski(k1_tarski(A_44), B_45) | ~r2_hidden(A_44, B_45))), inference(resolution, [status(thm)], [c_87, c_18])).
% 5.75/2.09  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.75/2.09  tff(c_66, plain, (![A_38, B_39]: (r1_tarski(A_38, B_39) | ~m1_subset_1(A_38, k1_zfmisc_1(B_39)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.75/2.09  tff(c_70, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_66])).
% 5.75/2.09  tff(c_108, plain, (![A_52, B_53]: (r2_hidden('#skF_2'(A_52, B_53), A_52) | r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.75/2.09  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.75/2.09  tff(c_116, plain, (![A_52]: (r1_tarski(A_52, A_52))), inference(resolution, [status(thm)], [c_108, c_8])).
% 5.75/2.09  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.75/2.09  tff(c_128, plain, (![C_57, B_58, A_59]: (r2_hidden(C_57, B_58) | ~r2_hidden(C_57, A_59) | ~r1_tarski(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.75/2.09  tff(c_248, plain, (![A_73, B_74, B_75]: (r2_hidden('#skF_2'(A_73, B_74), B_75) | ~r1_tarski(A_73, B_75) | r1_tarski(A_73, B_74))), inference(resolution, [status(thm)], [c_10, c_128])).
% 5.75/2.09  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.75/2.09  tff(c_393, plain, (![A_102, B_103, B_104, B_105]: (r2_hidden('#skF_2'(A_102, B_103), B_104) | ~r1_tarski(B_105, B_104) | ~r1_tarski(A_102, B_105) | r1_tarski(A_102, B_103))), inference(resolution, [status(thm)], [c_248, c_6])).
% 5.75/2.09  tff(c_552, plain, (![A_119, B_120, B_121, A_122]: (r2_hidden('#skF_2'(A_119, B_120), B_121) | ~r1_tarski(A_119, k1_tarski(A_122)) | r1_tarski(A_119, B_120) | ~r2_hidden(A_122, B_121))), inference(resolution, [status(thm)], [c_95, c_393])).
% 5.75/2.09  tff(c_565, plain, (![A_123, B_124, B_125]: (r2_hidden('#skF_2'(k1_tarski(A_123), B_124), B_125) | r1_tarski(k1_tarski(A_123), B_124) | ~r2_hidden(A_123, B_125))), inference(resolution, [status(thm)], [c_116, c_552])).
% 5.75/2.09  tff(c_2457, plain, (![A_240, B_241, B_242, B_243]: (r2_hidden('#skF_2'(k1_tarski(A_240), B_241), B_242) | ~r1_tarski(B_243, B_242) | r1_tarski(k1_tarski(A_240), B_241) | ~r2_hidden(A_240, B_243))), inference(resolution, [status(thm)], [c_565, c_6])).
% 5.75/2.09  tff(c_2482, plain, (![A_244, B_245]: (r2_hidden('#skF_2'(k1_tarski(A_244), B_245), u1_struct_0('#skF_4')) | r1_tarski(k1_tarski(A_244), B_245) | ~r2_hidden(A_244, '#skF_5'))), inference(resolution, [status(thm)], [c_70, c_2457])).
% 5.75/2.09  tff(c_2499, plain, (![A_244]: (r1_tarski(k1_tarski(A_244), u1_struct_0('#skF_4')) | ~r2_hidden(A_244, '#skF_5'))), inference(resolution, [status(thm)], [c_2482, c_8])).
% 5.83/2.09  tff(c_46, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.83/2.09  tff(c_44, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.83/2.09  tff(c_42, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.83/2.09  tff(c_38, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.83/2.09  tff(c_20, plain, (![A_16, B_17]: (m1_subset_1(A_16, k1_zfmisc_1(B_17)) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.83/2.09  tff(c_458, plain, (![A_109, B_110, C_111]: (k9_subset_1(u1_struct_0(A_109), B_110, k2_pre_topc(A_109, C_111))=C_111 | ~r1_tarski(C_111, B_110) | ~m1_subset_1(C_111, k1_zfmisc_1(u1_struct_0(A_109))) | ~v2_tex_2(B_110, A_109) | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0(A_109))) | ~l1_pre_topc(A_109) | ~v2_pre_topc(A_109) | v2_struct_0(A_109))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.83/2.09  tff(c_2988, plain, (![A_268, B_269, A_270]: (k9_subset_1(u1_struct_0(A_268), B_269, k2_pre_topc(A_268, A_270))=A_270 | ~r1_tarski(A_270, B_269) | ~v2_tex_2(B_269, A_268) | ~m1_subset_1(B_269, k1_zfmisc_1(u1_struct_0(A_268))) | ~l1_pre_topc(A_268) | ~v2_pre_topc(A_268) | v2_struct_0(A_268) | ~r1_tarski(A_270, u1_struct_0(A_268)))), inference(resolution, [status(thm)], [c_20, c_458])).
% 5.83/2.09  tff(c_2998, plain, (![A_270]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', A_270))=A_270 | ~r1_tarski(A_270, '#skF_5') | ~v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~r1_tarski(A_270, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_40, c_2988])).
% 5.83/2.09  tff(c_3004, plain, (![A_270]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', A_270))=A_270 | ~r1_tarski(A_270, '#skF_5') | v2_struct_0('#skF_4') | ~r1_tarski(A_270, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_38, c_2998])).
% 5.83/2.09  tff(c_3073, plain, (![A_273]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', A_273))=A_273 | ~r1_tarski(A_273, '#skF_5') | ~r1_tarski(A_273, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_46, c_3004])).
% 5.83/2.09  tff(c_47, plain, (![B_34, A_35]: (~r2_hidden(B_34, A_35) | ~v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.83/2.09  tff(c_51, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_34, c_47])).
% 5.83/2.09  tff(c_76, plain, (![B_42, A_43]: (v1_xboole_0(B_42) | ~m1_subset_1(B_42, k1_zfmisc_1(A_43)) | ~v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.83/2.09  tff(c_82, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_76])).
% 5.83/2.09  tff(c_86, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_51, c_82])).
% 5.83/2.09  tff(c_36, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.83/2.09  tff(c_138, plain, (![A_60, B_61]: (k6_domain_1(A_60, B_61)=k1_tarski(B_61) | ~m1_subset_1(B_61, A_60) | v1_xboole_0(A_60))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.83/2.09  tff(c_150, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_36, c_138])).
% 5.83/2.09  tff(c_156, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')=k1_tarski('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_86, c_150])).
% 5.83/2.09  tff(c_32, plain, (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')))!=k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.83/2.09  tff(c_180, plain, (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', k1_tarski('#skF_6')))!=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_156, c_156, c_32])).
% 5.83/2.09  tff(c_3112, plain, (~r1_tarski(k1_tarski('#skF_6'), '#skF_5') | ~r1_tarski(k1_tarski('#skF_6'), u1_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3073, c_180])).
% 5.83/2.09  tff(c_3120, plain, (~r1_tarski(k1_tarski('#skF_6'), u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_3112])).
% 5.83/2.09  tff(c_3123, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_2499, c_3120])).
% 5.83/2.09  tff(c_3136, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_3123])).
% 5.83/2.09  tff(c_3137, plain, (~r1_tarski(k1_tarski('#skF_6'), '#skF_5')), inference(splitRight, [status(thm)], [c_3112])).
% 5.83/2.09  tff(c_3144, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_95, c_3137])).
% 5.83/2.09  tff(c_3149, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_3144])).
% 5.83/2.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.83/2.09  
% 5.83/2.09  Inference rules
% 5.83/2.09  ----------------------
% 5.83/2.09  #Ref     : 0
% 5.83/2.09  #Sup     : 797
% 5.83/2.09  #Fact    : 0
% 5.83/2.09  #Define  : 0
% 5.83/2.09  #Split   : 9
% 5.83/2.09  #Chain   : 0
% 5.83/2.10  #Close   : 0
% 5.83/2.10  
% 5.83/2.10  Ordering : KBO
% 5.83/2.10  
% 5.83/2.10  Simplification rules
% 5.83/2.10  ----------------------
% 5.83/2.10  #Subsume      : 175
% 5.83/2.10  #Demod        : 126
% 5.83/2.10  #Tautology    : 92
% 5.83/2.10  #SimpNegUnit  : 17
% 5.83/2.10  #BackRed      : 1
% 5.83/2.10  
% 5.83/2.10  #Partial instantiations: 0
% 5.83/2.10  #Strategies tried      : 1
% 5.83/2.10  
% 5.83/2.10  Timing (in seconds)
% 5.83/2.10  ----------------------
% 5.83/2.10  Preprocessing        : 0.31
% 5.83/2.10  Parsing              : 0.17
% 5.83/2.10  CNF conversion       : 0.02
% 5.83/2.10  Main loop            : 1.01
% 5.83/2.10  Inferencing          : 0.29
% 5.83/2.10  Reduction            : 0.27
% 5.83/2.10  Demodulation         : 0.16
% 5.83/2.10  BG Simplification    : 0.04
% 5.83/2.10  Subsumption          : 0.34
% 5.83/2.10  Abstraction          : 0.04
% 5.83/2.10  MUC search           : 0.00
% 5.83/2.10  Cooper               : 0.00
% 5.83/2.10  Total                : 1.35
% 5.83/2.10  Index Insertion      : 0.00
% 5.83/2.10  Index Deletion       : 0.00
% 5.83/2.10  Index Matching       : 0.00
% 5.83/2.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
