%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:12 EST 2020

% Result     : Theorem 14.56s
% Output     : CNFRefutation 14.56s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 161 expanded)
%              Number of leaves         :   23 (  65 expanded)
%              Depth                    :   10
%              Number of atoms          :  119 ( 384 expanded)
%              Number of equality atoms :   10 (  36 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_82,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v2_tex_2(B,A)
                    | v2_tex_2(C,A) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tex_2)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( r1_tarski(C,B)
                  & v2_tex_2(B,A) )
               => v2_tex_2(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tex_2)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(A_16,k1_zfmisc_1(B_17))
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_305,plain,(
    ! [A_77,B_78,C_79] :
      ( k9_subset_1(A_77,B_78,C_79) = k3_xboole_0(B_78,C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(A_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_316,plain,(
    ! [B_78] : k9_subset_1(u1_struct_0('#skF_1'),B_78,'#skF_3') = k3_xboole_0(B_78,'#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_305])).

tff(c_24,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_352,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_24])).

tff(c_26,plain,
    ( v2_tex_2('#skF_3','#skF_1')
    | v2_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_36,plain,(
    v2_tex_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_353,plain,(
    ! [B_83] : k9_subset_1(u1_struct_0('#skF_1'),B_83,'#skF_3') = k3_xboole_0(B_83,'#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_305])).

tff(c_12,plain,(
    ! [A_8,B_9,C_10] :
      ( m1_subset_1(k9_subset_1(A_8,B_9,C_10),k1_zfmisc_1(A_8))
      | ~ m1_subset_1(C_10,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_362,plain,(
    ! [B_83] :
      ( m1_subset_1(k3_xboole_0(B_83,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_353,c_12])).

tff(c_370,plain,(
    ! [B_83] : m1_subset_1(k3_xboole_0(B_83,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_362])).

tff(c_8,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_318,plain,(
    ! [C_80,A_81,B_82] :
      ( v2_tex_2(C_80,A_81)
      | ~ v2_tex_2(B_82,A_81)
      | ~ r1_tarski(C_80,B_82)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_pre_topc(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_989,plain,(
    ! [A_140,B_141,A_142] :
      ( v2_tex_2(k3_xboole_0(A_140,B_141),A_142)
      | ~ v2_tex_2(A_140,A_142)
      | ~ m1_subset_1(k3_xboole_0(A_140,B_141),k1_zfmisc_1(u1_struct_0(A_142)))
      | ~ m1_subset_1(A_140,k1_zfmisc_1(u1_struct_0(A_142)))
      | ~ l1_pre_topc(A_142) ) ),
    inference(resolution,[status(thm)],[c_8,c_318])).

tff(c_1002,plain,(
    ! [B_83] :
      ( v2_tex_2(k3_xboole_0(B_83,'#skF_3'),'#skF_1')
      | ~ v2_tex_2(B_83,'#skF_1')
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_370,c_989])).

tff(c_2314,plain,(
    ! [B_237] :
      ( v2_tex_2(k3_xboole_0(B_237,'#skF_3'),'#skF_1')
      | ~ v2_tex_2(B_237,'#skF_1')
      | ~ m1_subset_1(B_237,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1002])).

tff(c_2344,plain,
    ( v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | ~ v2_tex_2('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_2314])).

tff(c_2355,plain,(
    v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2344])).

tff(c_2357,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_352,c_2355])).

tff(c_2358,plain,(
    v2_tex_2('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_2628,plain,(
    ! [A_283,B_284,C_285] :
      ( k9_subset_1(A_283,B_284,C_285) = k3_xboole_0(B_284,C_285)
      | ~ m1_subset_1(C_285,k1_zfmisc_1(A_283)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2642,plain,(
    ! [B_286] : k9_subset_1(u1_struct_0('#skF_1'),B_286,'#skF_3') = k3_xboole_0(B_286,'#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_2628])).

tff(c_2651,plain,(
    ! [B_286] :
      ( m1_subset_1(k3_xboole_0(B_286,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2642,c_12])).

tff(c_2659,plain,(
    ! [B_286] : m1_subset_1(k3_xboole_0(B_286,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2651])).

tff(c_2840,plain,(
    ! [B_301,B_302,A_303] :
      ( k9_subset_1(B_301,B_302,A_303) = k3_xboole_0(B_302,A_303)
      | ~ r1_tarski(A_303,B_301) ) ),
    inference(resolution,[status(thm)],[c_20,c_2628])).

tff(c_2884,plain,(
    ! [B_2,B_302] : k9_subset_1(B_2,B_302,B_2) = k3_xboole_0(B_302,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_2840])).

tff(c_2492,plain,(
    ! [A_265,B_266,C_267] :
      ( m1_subset_1(k9_subset_1(A_265,B_266,C_267),k1_zfmisc_1(A_265))
      | ~ m1_subset_1(C_267,k1_zfmisc_1(A_265)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(A_16,B_17)
      | ~ m1_subset_1(A_16,k1_zfmisc_1(B_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2496,plain,(
    ! [A_265,B_266,C_267] :
      ( r1_tarski(k9_subset_1(A_265,B_266,C_267),A_265)
      | ~ m1_subset_1(C_267,k1_zfmisc_1(A_265)) ) ),
    inference(resolution,[status(thm)],[c_2492,c_18])).

tff(c_2661,plain,(
    ! [C_287,A_288,B_289] :
      ( v2_tex_2(C_287,A_288)
      | ~ v2_tex_2(B_289,A_288)
      | ~ r1_tarski(C_287,B_289)
      | ~ m1_subset_1(C_287,k1_zfmisc_1(u1_struct_0(A_288)))
      | ~ m1_subset_1(B_289,k1_zfmisc_1(u1_struct_0(A_288)))
      | ~ l1_pre_topc(A_288) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_5980,plain,(
    ! [A_532,B_533,C_534,A_535] :
      ( v2_tex_2(k9_subset_1(A_532,B_533,C_534),A_535)
      | ~ v2_tex_2(A_532,A_535)
      | ~ m1_subset_1(k9_subset_1(A_532,B_533,C_534),k1_zfmisc_1(u1_struct_0(A_535)))
      | ~ m1_subset_1(A_532,k1_zfmisc_1(u1_struct_0(A_535)))
      | ~ l1_pre_topc(A_535)
      | ~ m1_subset_1(C_534,k1_zfmisc_1(A_532)) ) ),
    inference(resolution,[status(thm)],[c_2496,c_2661])).

tff(c_6010,plain,(
    ! [B_2,B_302,A_535] :
      ( v2_tex_2(k9_subset_1(B_2,B_302,B_2),A_535)
      | ~ v2_tex_2(B_2,A_535)
      | ~ m1_subset_1(k3_xboole_0(B_302,B_2),k1_zfmisc_1(u1_struct_0(A_535)))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(u1_struct_0(A_535)))
      | ~ l1_pre_topc(A_535)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2884,c_5980])).

tff(c_30985,plain,(
    ! [B_1641,B_1642,A_1643] :
      ( v2_tex_2(k3_xboole_0(B_1641,B_1642),A_1643)
      | ~ v2_tex_2(B_1642,A_1643)
      | ~ m1_subset_1(k3_xboole_0(B_1641,B_1642),k1_zfmisc_1(u1_struct_0(A_1643)))
      | ~ m1_subset_1(B_1642,k1_zfmisc_1(u1_struct_0(A_1643)))
      | ~ l1_pre_topc(A_1643)
      | ~ m1_subset_1(B_1642,k1_zfmisc_1(B_1642)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2884,c_6010])).

tff(c_31024,plain,(
    ! [B_286] :
      ( v2_tex_2(k3_xboole_0(B_286,'#skF_3'),'#skF_1')
      | ~ v2_tex_2('#skF_3','#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_2659,c_30985])).

tff(c_31068,plain,(
    ! [B_286] :
      ( v2_tex_2(k3_xboole_0(B_286,'#skF_3'),'#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_2358,c_31024])).

tff(c_31070,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_31068])).

tff(c_31073,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_31070])).

tff(c_31077,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_31073])).

tff(c_31078,plain,(
    ! [B_286] : v2_tex_2(k3_xboole_0(B_286,'#skF_3'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_31068])).

tff(c_2639,plain,(
    ! [B_284] : k9_subset_1(u1_struct_0('#skF_1'),B_284,'#skF_3') = k3_xboole_0(B_284,'#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_2628])).

tff(c_2641,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2639,c_24])).

tff(c_31127,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_31078,c_2641])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:05:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.56/7.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.56/7.10  
% 14.56/7.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.56/7.10  %$ v2_tex_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 14.56/7.10  
% 14.56/7.10  %Foreground sorts:
% 14.56/7.10  
% 14.56/7.10  
% 14.56/7.10  %Background operators:
% 14.56/7.10  
% 14.56/7.10  
% 14.56/7.10  %Foreground operators:
% 14.56/7.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.56/7.10  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 14.56/7.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.56/7.10  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 14.56/7.10  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 14.56/7.10  tff('#skF_2', type, '#skF_2': $i).
% 14.56/7.10  tff('#skF_3', type, '#skF_3': $i).
% 14.56/7.10  tff('#skF_1', type, '#skF_1': $i).
% 14.56/7.10  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.56/7.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.56/7.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.56/7.10  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.56/7.10  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 14.56/7.10  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 14.56/7.10  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.56/7.10  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 14.56/7.10  
% 14.56/7.12  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 14.56/7.12  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 14.56/7.12  tff(f_82, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(B, A) | v2_tex_2(C, A)) => v2_tex_2(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tex_2)).
% 14.56/7.12  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 14.56/7.12  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 14.56/7.12  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 14.56/7.12  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v2_tex_2(B, A)) => v2_tex_2(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_tex_2)).
% 14.56/7.12  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.56/7.12  tff(c_20, plain, (![A_16, B_17]: (m1_subset_1(A_16, k1_zfmisc_1(B_17)) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_53])).
% 14.56/7.12  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 14.56/7.12  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 14.56/7.12  tff(c_305, plain, (![A_77, B_78, C_79]: (k9_subset_1(A_77, B_78, C_79)=k3_xboole_0(B_78, C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(A_77)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.56/7.12  tff(c_316, plain, (![B_78]: (k9_subset_1(u1_struct_0('#skF_1'), B_78, '#skF_3')=k3_xboole_0(B_78, '#skF_3'))), inference(resolution, [status(thm)], [c_28, c_305])).
% 14.56/7.12  tff(c_24, plain, (~v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 14.56/7.12  tff(c_352, plain, (~v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_316, c_24])).
% 14.56/7.12  tff(c_26, plain, (v2_tex_2('#skF_3', '#skF_1') | v2_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 14.56/7.12  tff(c_36, plain, (v2_tex_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_26])).
% 14.56/7.12  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 14.56/7.12  tff(c_353, plain, (![B_83]: (k9_subset_1(u1_struct_0('#skF_1'), B_83, '#skF_3')=k3_xboole_0(B_83, '#skF_3'))), inference(resolution, [status(thm)], [c_28, c_305])).
% 14.56/7.12  tff(c_12, plain, (![A_8, B_9, C_10]: (m1_subset_1(k9_subset_1(A_8, B_9, C_10), k1_zfmisc_1(A_8)) | ~m1_subset_1(C_10, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 14.56/7.12  tff(c_362, plain, (![B_83]: (m1_subset_1(k3_xboole_0(B_83, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_353, c_12])).
% 14.56/7.12  tff(c_370, plain, (![B_83]: (m1_subset_1(k3_xboole_0(B_83, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_362])).
% 14.56/7.12  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 14.56/7.12  tff(c_318, plain, (![C_80, A_81, B_82]: (v2_tex_2(C_80, A_81) | ~v2_tex_2(B_82, A_81) | ~r1_tarski(C_80, B_82) | ~m1_subset_1(C_80, k1_zfmisc_1(u1_struct_0(A_81))) | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_pre_topc(A_81))), inference(cnfTransformation, [status(thm)], [f_67])).
% 14.56/7.12  tff(c_989, plain, (![A_140, B_141, A_142]: (v2_tex_2(k3_xboole_0(A_140, B_141), A_142) | ~v2_tex_2(A_140, A_142) | ~m1_subset_1(k3_xboole_0(A_140, B_141), k1_zfmisc_1(u1_struct_0(A_142))) | ~m1_subset_1(A_140, k1_zfmisc_1(u1_struct_0(A_142))) | ~l1_pre_topc(A_142))), inference(resolution, [status(thm)], [c_8, c_318])).
% 14.56/7.12  tff(c_1002, plain, (![B_83]: (v2_tex_2(k3_xboole_0(B_83, '#skF_3'), '#skF_1') | ~v2_tex_2(B_83, '#skF_1') | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_370, c_989])).
% 14.56/7.12  tff(c_2314, plain, (![B_237]: (v2_tex_2(k3_xboole_0(B_237, '#skF_3'), '#skF_1') | ~v2_tex_2(B_237, '#skF_1') | ~m1_subset_1(B_237, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1002])).
% 14.56/7.12  tff(c_2344, plain, (v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1') | ~v2_tex_2('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_30, c_2314])).
% 14.56/7.12  tff(c_2355, plain, (v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2344])).
% 14.56/7.12  tff(c_2357, plain, $false, inference(negUnitSimplification, [status(thm)], [c_352, c_2355])).
% 14.56/7.12  tff(c_2358, plain, (v2_tex_2('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_26])).
% 14.56/7.12  tff(c_2628, plain, (![A_283, B_284, C_285]: (k9_subset_1(A_283, B_284, C_285)=k3_xboole_0(B_284, C_285) | ~m1_subset_1(C_285, k1_zfmisc_1(A_283)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.56/7.12  tff(c_2642, plain, (![B_286]: (k9_subset_1(u1_struct_0('#skF_1'), B_286, '#skF_3')=k3_xboole_0(B_286, '#skF_3'))), inference(resolution, [status(thm)], [c_28, c_2628])).
% 14.56/7.12  tff(c_2651, plain, (![B_286]: (m1_subset_1(k3_xboole_0(B_286, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_2642, c_12])).
% 14.56/7.12  tff(c_2659, plain, (![B_286]: (m1_subset_1(k3_xboole_0(B_286, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_2651])).
% 14.56/7.12  tff(c_2840, plain, (![B_301, B_302, A_303]: (k9_subset_1(B_301, B_302, A_303)=k3_xboole_0(B_302, A_303) | ~r1_tarski(A_303, B_301))), inference(resolution, [status(thm)], [c_20, c_2628])).
% 14.56/7.12  tff(c_2884, plain, (![B_2, B_302]: (k9_subset_1(B_2, B_302, B_2)=k3_xboole_0(B_302, B_2))), inference(resolution, [status(thm)], [c_6, c_2840])).
% 14.56/7.12  tff(c_2492, plain, (![A_265, B_266, C_267]: (m1_subset_1(k9_subset_1(A_265, B_266, C_267), k1_zfmisc_1(A_265)) | ~m1_subset_1(C_267, k1_zfmisc_1(A_265)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 14.56/7.12  tff(c_18, plain, (![A_16, B_17]: (r1_tarski(A_16, B_17) | ~m1_subset_1(A_16, k1_zfmisc_1(B_17)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 14.56/7.12  tff(c_2496, plain, (![A_265, B_266, C_267]: (r1_tarski(k9_subset_1(A_265, B_266, C_267), A_265) | ~m1_subset_1(C_267, k1_zfmisc_1(A_265)))), inference(resolution, [status(thm)], [c_2492, c_18])).
% 14.56/7.12  tff(c_2661, plain, (![C_287, A_288, B_289]: (v2_tex_2(C_287, A_288) | ~v2_tex_2(B_289, A_288) | ~r1_tarski(C_287, B_289) | ~m1_subset_1(C_287, k1_zfmisc_1(u1_struct_0(A_288))) | ~m1_subset_1(B_289, k1_zfmisc_1(u1_struct_0(A_288))) | ~l1_pre_topc(A_288))), inference(cnfTransformation, [status(thm)], [f_67])).
% 14.56/7.12  tff(c_5980, plain, (![A_532, B_533, C_534, A_535]: (v2_tex_2(k9_subset_1(A_532, B_533, C_534), A_535) | ~v2_tex_2(A_532, A_535) | ~m1_subset_1(k9_subset_1(A_532, B_533, C_534), k1_zfmisc_1(u1_struct_0(A_535))) | ~m1_subset_1(A_532, k1_zfmisc_1(u1_struct_0(A_535))) | ~l1_pre_topc(A_535) | ~m1_subset_1(C_534, k1_zfmisc_1(A_532)))), inference(resolution, [status(thm)], [c_2496, c_2661])).
% 14.56/7.12  tff(c_6010, plain, (![B_2, B_302, A_535]: (v2_tex_2(k9_subset_1(B_2, B_302, B_2), A_535) | ~v2_tex_2(B_2, A_535) | ~m1_subset_1(k3_xboole_0(B_302, B_2), k1_zfmisc_1(u1_struct_0(A_535))) | ~m1_subset_1(B_2, k1_zfmisc_1(u1_struct_0(A_535))) | ~l1_pre_topc(A_535) | ~m1_subset_1(B_2, k1_zfmisc_1(B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2884, c_5980])).
% 14.56/7.12  tff(c_30985, plain, (![B_1641, B_1642, A_1643]: (v2_tex_2(k3_xboole_0(B_1641, B_1642), A_1643) | ~v2_tex_2(B_1642, A_1643) | ~m1_subset_1(k3_xboole_0(B_1641, B_1642), k1_zfmisc_1(u1_struct_0(A_1643))) | ~m1_subset_1(B_1642, k1_zfmisc_1(u1_struct_0(A_1643))) | ~l1_pre_topc(A_1643) | ~m1_subset_1(B_1642, k1_zfmisc_1(B_1642)))), inference(demodulation, [status(thm), theory('equality')], [c_2884, c_6010])).
% 14.56/7.12  tff(c_31024, plain, (![B_286]: (v2_tex_2(k3_xboole_0(B_286, '#skF_3'), '#skF_1') | ~v2_tex_2('#skF_3', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_2659, c_30985])).
% 14.56/7.12  tff(c_31068, plain, (![B_286]: (v2_tex_2(k3_xboole_0(B_286, '#skF_3'), '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_2358, c_31024])).
% 14.56/7.12  tff(c_31070, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_31068])).
% 14.56/7.12  tff(c_31073, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_20, c_31070])).
% 14.56/7.12  tff(c_31077, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_31073])).
% 14.56/7.12  tff(c_31078, plain, (![B_286]: (v2_tex_2(k3_xboole_0(B_286, '#skF_3'), '#skF_1'))), inference(splitRight, [status(thm)], [c_31068])).
% 14.56/7.12  tff(c_2639, plain, (![B_284]: (k9_subset_1(u1_struct_0('#skF_1'), B_284, '#skF_3')=k3_xboole_0(B_284, '#skF_3'))), inference(resolution, [status(thm)], [c_28, c_2628])).
% 14.56/7.12  tff(c_2641, plain, (~v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2639, c_24])).
% 14.56/7.12  tff(c_31127, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_31078, c_2641])).
% 14.56/7.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.56/7.12  
% 14.56/7.12  Inference rules
% 14.56/7.12  ----------------------
% 14.56/7.12  #Ref     : 0
% 14.56/7.12  #Sup     : 6885
% 14.56/7.12  #Fact    : 0
% 14.56/7.12  #Define  : 0
% 14.56/7.12  #Split   : 8
% 14.56/7.12  #Chain   : 0
% 14.56/7.12  #Close   : 0
% 14.56/7.12  
% 14.56/7.12  Ordering : KBO
% 14.56/7.12  
% 14.56/7.12  Simplification rules
% 14.56/7.12  ----------------------
% 14.56/7.12  #Subsume      : 680
% 14.56/7.12  #Demod        : 1512
% 14.56/7.12  #Tautology    : 749
% 14.56/7.12  #SimpNegUnit  : 8
% 14.56/7.12  #BackRed      : 4
% 14.56/7.12  
% 14.56/7.12  #Partial instantiations: 0
% 14.56/7.12  #Strategies tried      : 1
% 14.56/7.12  
% 14.56/7.12  Timing (in seconds)
% 14.56/7.12  ----------------------
% 14.56/7.12  Preprocessing        : 0.32
% 14.56/7.12  Parsing              : 0.17
% 14.56/7.12  CNF conversion       : 0.02
% 14.56/7.12  Main loop            : 6.05
% 14.56/7.12  Inferencing          : 1.18
% 14.56/7.12  Reduction            : 2.13
% 14.56/7.12  Demodulation         : 1.77
% 14.56/7.12  BG Simplification    : 0.14
% 14.56/7.12  Subsumption          : 2.23
% 14.56/7.12  Abstraction          : 0.19
% 14.56/7.12  MUC search           : 0.00
% 14.56/7.12  Cooper               : 0.00
% 14.56/7.12  Total                : 6.40
% 14.56/7.12  Index Insertion      : 0.00
% 14.56/7.12  Index Deletion       : 0.00
% 14.56/7.12  Index Matching       : 0.00
% 14.56/7.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
