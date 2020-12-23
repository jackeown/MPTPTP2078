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
% DateTime   : Thu Dec  3 10:29:43 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.41s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 150 expanded)
%              Number of leaves         :   30 (  65 expanded)
%              Depth                    :   12
%              Number of atoms          :  120 ( 392 expanded)
%              Number of equality atoms :   14 (  43 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_106,negated_conjecture,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_86,axiom,(
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

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_36,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_71,plain,(
    ! [A_43,B_44] :
      ( r2_hidden('#skF_1'(A_43,B_44),A_43)
      | r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_79,plain,(
    ! [A_43] : r1_tarski(A_43,A_43) ),
    inference(resolution,[status(thm)],[c_71,c_4])).

tff(c_32,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_88,plain,(
    ! [C_48,B_49,A_50] :
      ( ~ v1_xboole_0(C_48)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(C_48))
      | ~ r2_hidden(A_50,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_100,plain,(
    ! [B_51,A_52,A_53] :
      ( ~ v1_xboole_0(B_51)
      | ~ r2_hidden(A_52,A_53)
      | ~ r1_tarski(A_53,B_51) ) ),
    inference(resolution,[status(thm)],[c_14,c_88])).

tff(c_110,plain,(
    ! [B_54] :
      ( ~ v1_xboole_0(B_54)
      | ~ r1_tarski('#skF_4',B_54) ) ),
    inference(resolution,[status(thm)],[c_32,c_100])).

tff(c_118,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_79,c_110])).

tff(c_45,plain,(
    ! [A_33,B_34] :
      ( m1_subset_1(A_33,B_34)
      | ~ r2_hidden(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_49,plain,(
    m1_subset_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_45])).

tff(c_232,plain,(
    ! [A_71,B_72] :
      ( k6_domain_1(A_71,B_72) = k1_tarski(B_72)
      | ~ m1_subset_1(B_72,A_71)
      | v1_xboole_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_241,plain,
    ( k6_domain_1('#skF_4','#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_49,c_232])).

tff(c_252,plain,(
    k6_domain_1('#skF_4','#skF_5') = k1_tarski('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_241])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(k6_domain_1(A_15,B_16),k1_zfmisc_1(A_15))
      | ~ m1_subset_1(B_16,A_15)
      | v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_272,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5','#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_18])).

tff(c_276,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_272])).

tff(c_277,plain,(
    m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_276])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_289,plain,(
    r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_277,c_12])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_42,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_40,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_98,plain,(
    ! [A_50] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_50,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_38,c_88])).

tff(c_99,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_247,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_232])).

tff(c_256,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') = k1_tarski('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_247])).

tff(c_305,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_18])).

tff(c_309,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_305])).

tff(c_310,plain,(
    m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_309])).

tff(c_739,plain,(
    ! [A_123,B_124,C_125] :
      ( k9_subset_1(u1_struct_0(A_123),B_124,k2_pre_topc(A_123,C_125)) = C_125
      | ~ r1_tarski(C_125,B_124)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ v2_tex_2(B_124,A_123)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_pre_topc(A_123)
      | ~ v2_pre_topc(A_123)
      | v2_struct_0(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_746,plain,(
    ! [B_124] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_124,k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) = k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski('#skF_5'),B_124)
      | ~ v2_tex_2(B_124,'#skF_3')
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_310,c_739])).

tff(c_762,plain,(
    ! [B_124] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_124,k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) = k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski('#skF_5'),B_124)
      | ~ v2_tex_2(B_124,'#skF_3')
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_746])).

tff(c_1017,plain,(
    ! [B_142] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_142,k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) = k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski('#skF_5'),B_142)
      | ~ v2_tex_2(B_142,'#skF_3')
      | ~ m1_subset_1(B_142,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_762])).

tff(c_30,plain,(
    k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5'))) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_301,plain,(
    k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) != k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_256,c_30])).

tff(c_1023,plain,
    ( ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1017,c_301])).

tff(c_1031,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_289,c_1023])).

tff(c_1032,plain,(
    ! [A_50] : ~ r2_hidden(A_50,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_1035,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1032,c_32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:03:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.02/1.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.63  
% 3.02/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.63  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.02/1.63  
% 3.02/1.63  %Foreground sorts:
% 3.02/1.63  
% 3.02/1.63  
% 3.02/1.63  %Background operators:
% 3.02/1.63  
% 3.02/1.63  
% 3.02/1.63  %Foreground operators:
% 3.02/1.63  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.02/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.02/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.02/1.63  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.02/1.63  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.02/1.63  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.02/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.02/1.63  tff('#skF_5', type, '#skF_5': $i).
% 3.02/1.63  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.02/1.63  tff('#skF_3', type, '#skF_3': $i).
% 3.02/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.02/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.02/1.63  tff('#skF_4', type, '#skF_4': $i).
% 3.02/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.02/1.63  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.02/1.63  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.02/1.63  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.02/1.63  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.02/1.63  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.02/1.63  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.02/1.63  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.02/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.02/1.63  
% 3.41/1.65  tff(f_106, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_tex_2)).
% 3.41/1.65  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.41/1.65  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.41/1.65  tff(f_53, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.41/1.65  tff(f_36, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 3.41/1.65  tff(f_67, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.41/1.65  tff(f_60, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 3.41/1.65  tff(f_86, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tex_2)).
% 3.41/1.65  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.41/1.65  tff(c_36, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.41/1.65  tff(c_71, plain, (![A_43, B_44]: (r2_hidden('#skF_1'(A_43, B_44), A_43) | r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.41/1.65  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.41/1.65  tff(c_79, plain, (![A_43]: (r1_tarski(A_43, A_43))), inference(resolution, [status(thm)], [c_71, c_4])).
% 3.41/1.65  tff(c_32, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.41/1.65  tff(c_14, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.41/1.65  tff(c_88, plain, (![C_48, B_49, A_50]: (~v1_xboole_0(C_48) | ~m1_subset_1(B_49, k1_zfmisc_1(C_48)) | ~r2_hidden(A_50, B_49))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.41/1.65  tff(c_100, plain, (![B_51, A_52, A_53]: (~v1_xboole_0(B_51) | ~r2_hidden(A_52, A_53) | ~r1_tarski(A_53, B_51))), inference(resolution, [status(thm)], [c_14, c_88])).
% 3.41/1.65  tff(c_110, plain, (![B_54]: (~v1_xboole_0(B_54) | ~r1_tarski('#skF_4', B_54))), inference(resolution, [status(thm)], [c_32, c_100])).
% 3.41/1.65  tff(c_118, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_79, c_110])).
% 3.41/1.65  tff(c_45, plain, (![A_33, B_34]: (m1_subset_1(A_33, B_34) | ~r2_hidden(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.41/1.65  tff(c_49, plain, (m1_subset_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_32, c_45])).
% 3.41/1.65  tff(c_232, plain, (![A_71, B_72]: (k6_domain_1(A_71, B_72)=k1_tarski(B_72) | ~m1_subset_1(B_72, A_71) | v1_xboole_0(A_71))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.41/1.65  tff(c_241, plain, (k6_domain_1('#skF_4', '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_49, c_232])).
% 3.41/1.65  tff(c_252, plain, (k6_domain_1('#skF_4', '#skF_5')=k1_tarski('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_118, c_241])).
% 3.41/1.65  tff(c_18, plain, (![A_15, B_16]: (m1_subset_1(k6_domain_1(A_15, B_16), k1_zfmisc_1(A_15)) | ~m1_subset_1(B_16, A_15) | v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.41/1.65  tff(c_272, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', '#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_252, c_18])).
% 3.41/1.65  tff(c_276, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4')) | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_49, c_272])).
% 3.41/1.65  tff(c_277, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_118, c_276])).
% 3.41/1.65  tff(c_12, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.41/1.65  tff(c_289, plain, (r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_277, c_12])).
% 3.41/1.65  tff(c_44, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.41/1.65  tff(c_42, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.41/1.65  tff(c_40, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.41/1.65  tff(c_98, plain, (![A_50]: (~v1_xboole_0(u1_struct_0('#skF_3')) | ~r2_hidden(A_50, '#skF_4'))), inference(resolution, [status(thm)], [c_38, c_88])).
% 3.41/1.65  tff(c_99, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_98])).
% 3.41/1.65  tff(c_34, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.41/1.65  tff(c_247, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_232])).
% 3.41/1.65  tff(c_256, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')=k1_tarski('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_99, c_247])).
% 3.41/1.65  tff(c_305, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_256, c_18])).
% 3.41/1.65  tff(c_309, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_305])).
% 3.41/1.65  tff(c_310, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_99, c_309])).
% 3.41/1.65  tff(c_739, plain, (![A_123, B_124, C_125]: (k9_subset_1(u1_struct_0(A_123), B_124, k2_pre_topc(A_123, C_125))=C_125 | ~r1_tarski(C_125, B_124) | ~m1_subset_1(C_125, k1_zfmisc_1(u1_struct_0(A_123))) | ~v2_tex_2(B_124, A_123) | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0(A_123))) | ~l1_pre_topc(A_123) | ~v2_pre_topc(A_123) | v2_struct_0(A_123))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.41/1.65  tff(c_746, plain, (![B_124]: (k9_subset_1(u1_struct_0('#skF_3'), B_124, k2_pre_topc('#skF_3', k1_tarski('#skF_5')))=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski('#skF_5'), B_124) | ~v2_tex_2(B_124, '#skF_3') | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_310, c_739])).
% 3.41/1.65  tff(c_762, plain, (![B_124]: (k9_subset_1(u1_struct_0('#skF_3'), B_124, k2_pre_topc('#skF_3', k1_tarski('#skF_5')))=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski('#skF_5'), B_124) | ~v2_tex_2(B_124, '#skF_3') | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_746])).
% 3.41/1.65  tff(c_1017, plain, (![B_142]: (k9_subset_1(u1_struct_0('#skF_3'), B_142, k2_pre_topc('#skF_3', k1_tarski('#skF_5')))=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski('#skF_5'), B_142) | ~v2_tex_2(B_142, '#skF_3') | ~m1_subset_1(B_142, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_44, c_762])).
% 3.41/1.65  tff(c_30, plain, (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')))!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.41/1.65  tff(c_301, plain, (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k1_tarski('#skF_5')))!=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_256, c_256, c_30])).
% 3.41/1.65  tff(c_1023, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1017, c_301])).
% 3.41/1.65  tff(c_1031, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_289, c_1023])).
% 3.41/1.65  tff(c_1032, plain, (![A_50]: (~r2_hidden(A_50, '#skF_4'))), inference(splitRight, [status(thm)], [c_98])).
% 3.41/1.65  tff(c_1035, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1032, c_32])).
% 3.41/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.41/1.65  
% 3.41/1.65  Inference rules
% 3.41/1.65  ----------------------
% 3.41/1.65  #Ref     : 0
% 3.41/1.65  #Sup     : 232
% 3.41/1.65  #Fact    : 0
% 3.41/1.65  #Define  : 0
% 3.41/1.65  #Split   : 6
% 3.41/1.65  #Chain   : 0
% 3.41/1.65  #Close   : 0
% 3.41/1.65  
% 3.41/1.65  Ordering : KBO
% 3.41/1.65  
% 3.41/1.65  Simplification rules
% 3.41/1.65  ----------------------
% 3.41/1.65  #Subsume      : 53
% 3.41/1.65  #Demod        : 65
% 3.41/1.65  #Tautology    : 64
% 3.41/1.65  #SimpNegUnit  : 28
% 3.41/1.65  #BackRed      : 2
% 3.41/1.65  
% 3.41/1.65  #Partial instantiations: 0
% 3.41/1.65  #Strategies tried      : 1
% 3.41/1.65  
% 3.41/1.65  Timing (in seconds)
% 3.41/1.65  ----------------------
% 3.41/1.65  Preprocessing        : 0.35
% 3.41/1.65  Parsing              : 0.20
% 3.41/1.65  CNF conversion       : 0.03
% 3.41/1.65  Main loop            : 0.40
% 3.41/1.65  Inferencing          : 0.14
% 3.41/1.65  Reduction            : 0.12
% 3.41/1.65  Demodulation         : 0.08
% 3.41/1.65  BG Simplification    : 0.02
% 3.41/1.65  Subsumption          : 0.09
% 3.41/1.65  Abstraction          : 0.02
% 3.41/1.65  MUC search           : 0.00
% 3.41/1.65  Cooper               : 0.00
% 3.41/1.65  Total                : 0.79
% 3.41/1.65  Index Insertion      : 0.00
% 3.41/1.65  Index Deletion       : 0.00
% 3.41/1.65  Index Matching       : 0.00
% 3.41/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
