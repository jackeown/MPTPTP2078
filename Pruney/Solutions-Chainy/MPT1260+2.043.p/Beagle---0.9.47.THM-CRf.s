%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:05 EST 2020

% Result     : Theorem 49.39s
% Output     : CNFRefutation 49.52s
% Verified   : 
% Statistics : Number of formulae       :  179 ( 411 expanded)
%              Number of leaves         :   50 ( 156 expanded)
%              Depth                    :   11
%              Number of atoms          :  265 ( 798 expanded)
%              Number of equality atoms :  121 ( 288 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_171,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_159,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_73,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_152,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_109,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_71,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_47,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_63,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_117,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_138,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

tff(f_124,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_76,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') != k2_tops_1('#skF_1','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_122,plain,(
    ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_72,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_70,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_2920,plain,(
    ! [A_178,B_179,C_180] :
      ( k7_subset_1(A_178,B_179,C_180) = k4_xboole_0(B_179,C_180)
      | ~ m1_subset_1(B_179,k1_zfmisc_1(A_178)) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2929,plain,(
    ! [C_180] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_180) = k4_xboole_0('#skF_2',C_180) ),
    inference(resolution,[status(thm)],[c_70,c_2920])).

tff(c_4192,plain,(
    ! [A_215,B_216] :
      ( k7_subset_1(u1_struct_0(A_215),B_216,k2_tops_1(A_215,B_216)) = k1_tops_1(A_215,B_216)
      | ~ m1_subset_1(B_216,k1_zfmisc_1(u1_struct_0(A_215)))
      | ~ l1_pre_topc(A_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_4205,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_4192])).

tff(c_4212,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2929,c_4205])).

tff(c_38,plain,(
    ! [A_31,B_32] : k4_xboole_0(A_31,k4_xboole_0(A_31,B_32)) = k3_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4478,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4212,c_38])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | k4_xboole_0(A_7,B_8) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_26,plain,(
    ! [A_19,B_20] : r1_tarski(k4_xboole_0(A_19,B_20),A_19) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1166,plain,(
    ! [B_132,A_133] :
      ( B_132 = A_133
      | ~ r1_tarski(B_132,A_133)
      | ~ r1_tarski(A_133,B_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_11968,plain,(
    ! [A_349,B_350] :
      ( k4_xboole_0(A_349,B_350) = A_349
      | ~ r1_tarski(A_349,k4_xboole_0(A_349,B_350)) ) ),
    inference(resolution,[status(thm)],[c_26,c_1166])).

tff(c_12004,plain,
    ( k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4212,c_11968])).

tff(c_12070,plain,
    ( k1_tops_1('#skF_1','#skF_2') = '#skF_2'
    | ~ r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4212,c_12004])).

tff(c_49487,plain,(
    ~ r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_12070])).

tff(c_49495,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_49487])).

tff(c_99809,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4478,c_49495])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4731,plain,(
    ! [A_221,B_222] :
      ( k4_subset_1(u1_struct_0(A_221),B_222,k2_tops_1(A_221,B_222)) = k2_pre_topc(A_221,B_222)
      | ~ m1_subset_1(B_222,k1_zfmisc_1(u1_struct_0(A_221)))
      | ~ l1_pre_topc(A_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_4744,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_4731])).

tff(c_4751,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_4744])).

tff(c_56,plain,(
    ! [A_50,B_51] :
      ( m1_subset_1(k2_tops_1(A_50,B_51),k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_3638,plain,(
    ! [A_199,B_200,C_201] :
      ( k4_subset_1(A_199,B_200,C_201) = k2_xboole_0(B_200,C_201)
      | ~ m1_subset_1(C_201,k1_zfmisc_1(A_199))
      | ~ m1_subset_1(B_200,k1_zfmisc_1(A_199)) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_38572,plain,(
    ! [A_599,B_600,B_601] :
      ( k4_subset_1(u1_struct_0(A_599),B_600,k2_tops_1(A_599,B_601)) = k2_xboole_0(B_600,k2_tops_1(A_599,B_601))
      | ~ m1_subset_1(B_600,k1_zfmisc_1(u1_struct_0(A_599)))
      | ~ m1_subset_1(B_601,k1_zfmisc_1(u1_struct_0(A_599)))
      | ~ l1_pre_topc(A_599) ) ),
    inference(resolution,[status(thm)],[c_56,c_3638])).

tff(c_38588,plain,(
    ! [B_601] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_601)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_601))
      | ~ m1_subset_1(B_601,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_70,c_38572])).

tff(c_43765,plain,(
    ! [B_648] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_648)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_648))
      | ~ m1_subset_1(B_648,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_38588])).

tff(c_43788,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_70,c_43765])).

tff(c_43797,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4751,c_43788])).

tff(c_36,plain,(
    ! [A_29,B_30] : k4_xboole_0(A_29,k2_xboole_0(A_29,B_30)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_43982,plain,(
    k4_xboole_0('#skF_2',k2_pre_topc('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_43797,c_36])).

tff(c_20,plain,(
    ! [A_13] : k2_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_772,plain,(
    ! [A_115,B_116] : k4_xboole_0(A_115,k4_xboole_0(A_115,B_116)) = k3_xboole_0(A_115,B_116) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_837,plain,(
    ! [A_117,B_118] : r1_tarski(k3_xboole_0(A_117,B_118),A_117) ),
    inference(superposition,[status(thm),theory(equality)],[c_772,c_26])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( k4_xboole_0(A_7,B_8) = k1_xboole_0
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1505,plain,(
    ! [A_142,B_143] : k4_xboole_0(k3_xboole_0(A_142,B_143),A_142) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_837,c_14])).

tff(c_28,plain,(
    ! [A_21,B_22] : k2_xboole_0(A_21,k4_xboole_0(B_22,A_21)) = k2_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1510,plain,(
    ! [A_142,B_143] : k2_xboole_0(A_142,k3_xboole_0(A_142,B_143)) = k2_xboole_0(A_142,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1505,c_28])).

tff(c_1584,plain,(
    ! [A_144,B_145] : k2_xboole_0(A_144,k3_xboole_0(A_144,B_145)) = A_144 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1510])).

tff(c_1636,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k3_xboole_0(B_4,A_3)) = A_3 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1584])).

tff(c_650,plain,(
    ! [A_108,B_109] :
      ( k3_xboole_0(A_108,B_109) = A_108
      | ~ r1_tarski(A_108,B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6351,plain,(
    ! [A_258,B_259] : k3_xboole_0(k4_xboole_0(A_258,B_259),A_258) = k4_xboole_0(A_258,B_259) ),
    inference(resolution,[status(thm)],[c_26,c_650])).

tff(c_6412,plain,(
    ! [A_258,B_259] : k3_xboole_0(A_258,k4_xboole_0(A_258,B_259)) = k4_xboole_0(A_258,B_259) ),
    inference(superposition,[status(thm),theory(equality)],[c_6351,c_4])).

tff(c_797,plain,(
    ! [A_31,B_32] : k4_xboole_0(A_31,k3_xboole_0(A_31,B_32)) = k3_xboole_0(A_31,k4_xboole_0(A_31,B_32)) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_772])).

tff(c_18410,plain,(
    ! [A_412,B_413] : k4_xboole_0(A_412,k3_xboole_0(A_412,B_413)) = k4_xboole_0(A_412,B_413) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6412,c_797])).

tff(c_28684,plain,(
    ! [B_508,A_509] : k4_xboole_0(B_508,k3_xboole_0(A_509,B_508)) = k4_xboole_0(B_508,A_509) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_18410])).

tff(c_759,plain,(
    ! [A_113,B_114] :
      ( r1_tarski(A_113,B_114)
      | k4_xboole_0(A_113,B_114) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( k2_xboole_0(A_11,B_12) = B_12
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_770,plain,(
    ! [A_113,B_114] :
      ( k2_xboole_0(A_113,B_114) = B_114
      | k4_xboole_0(A_113,B_114) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_759,c_18])).

tff(c_28794,plain,(
    ! [B_508,A_509] :
      ( k2_xboole_0(B_508,k3_xboole_0(A_509,B_508)) = k3_xboole_0(A_509,B_508)
      | k4_xboole_0(B_508,A_509) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28684,c_770])).

tff(c_29000,plain,(
    ! [A_509,B_508] :
      ( k3_xboole_0(A_509,B_508) = B_508
      | k4_xboole_0(B_508,A_509) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1636,c_28794])).

tff(c_44715,plain,(
    k3_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_43982,c_29000])).

tff(c_82,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_310,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_82])).

tff(c_54,plain,(
    ! [A_48,B_49] :
      ( m1_subset_1(A_48,k1_zfmisc_1(B_49))
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_13024,plain,(
    ! [B_360,A_361,C_362] :
      ( k7_subset_1(B_360,A_361,C_362) = k4_xboole_0(A_361,C_362)
      | ~ r1_tarski(A_361,B_360) ) ),
    inference(resolution,[status(thm)],[c_54,c_2920])).

tff(c_110133,plain,(
    ! [B_958,A_959,C_960] :
      ( k7_subset_1(B_958,A_959,C_960) = k4_xboole_0(A_959,C_960)
      | k4_xboole_0(A_959,B_958) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_13024])).

tff(c_110218,plain,
    ( k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2')
    | k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),u1_struct_0('#skF_1')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_310,c_110133])).

tff(c_110994,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),u1_struct_0('#skF_1')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_110218])).

tff(c_3471,plain,(
    ! [A_194,B_195,C_196] :
      ( m1_subset_1(k4_subset_1(A_194,B_195,C_196),k1_zfmisc_1(A_194))
      | ~ m1_subset_1(C_196,k1_zfmisc_1(A_194))
      | ~ m1_subset_1(B_195,k1_zfmisc_1(A_194)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_52,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(A_48,B_49)
      | ~ m1_subset_1(A_48,k1_zfmisc_1(B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_20364,plain,(
    ! [A_428,B_429,C_430] :
      ( r1_tarski(k4_subset_1(A_428,B_429,C_430),A_428)
      | ~ m1_subset_1(C_430,k1_zfmisc_1(A_428))
      | ~ m1_subset_1(B_429,k1_zfmisc_1(A_428)) ) ),
    inference(resolution,[status(thm)],[c_3471,c_52])).

tff(c_20420,plain,
    ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_4751,c_20364])).

tff(c_20445,plain,
    ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_20420])).

tff(c_189681,plain,(
    ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_20445])).

tff(c_189684,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_189681])).

tff(c_189691,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_189684])).

tff(c_189692,plain,(
    r1_tarski(k2_pre_topc('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_20445])).

tff(c_189735,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),u1_struct_0('#skF_1')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_189692,c_14])).

tff(c_189756,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_110994,c_189735])).

tff(c_189758,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),u1_struct_0('#skF_1')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_110218])).

tff(c_110179,plain,
    ( k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2')
    | k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),u1_struct_0('#skF_1')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_110133,c_310])).

tff(c_190127,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_189758,c_110179])).

tff(c_108,plain,(
    ! [A_79,B_80] : k4_xboole_0(A_79,k2_xboole_0(A_79,B_80)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_118,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_108])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2074,plain,(
    ! [A_161,B_162] :
      ( k4_xboole_0(A_161,B_162) = k3_subset_1(A_161,B_162)
      | ~ m1_subset_1(B_162,k1_zfmisc_1(A_161)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_11633,plain,(
    ! [B_345,A_346] :
      ( k4_xboole_0(B_345,A_346) = k3_subset_1(B_345,A_346)
      | ~ r1_tarski(A_346,B_345) ) ),
    inference(resolution,[status(thm)],[c_54,c_2074])).

tff(c_11789,plain,(
    ! [B_6] : k4_xboole_0(B_6,B_6) = k3_subset_1(B_6,B_6) ),
    inference(resolution,[status(thm)],[c_10,c_11633])).

tff(c_11846,plain,(
    ! [B_6] : k3_subset_1(B_6,B_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_11789])).

tff(c_30,plain,(
    ! [A_23] : k4_xboole_0(A_23,k1_xboole_0) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_144,plain,(
    ! [B_83,A_84] : k2_xboole_0(B_83,A_84) = k2_xboole_0(A_84,B_83) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_162,plain,(
    ! [B_83,A_84] : k4_xboole_0(B_83,k2_xboole_0(A_84,B_83)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_36])).

tff(c_809,plain,(
    ! [B_83,A_84] : k3_xboole_0(B_83,k2_xboole_0(A_84,B_83)) = k4_xboole_0(B_83,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_772])).

tff(c_831,plain,(
    ! [B_83,A_84] : k3_xboole_0(B_83,k2_xboole_0(A_84,B_83)) = B_83 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_809])).

tff(c_32,plain,(
    ! [A_24,B_25] : k4_xboole_0(k2_xboole_0(A_24,B_25),B_25) = k4_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_7740,plain,(
    ! [A_283,B_284] :
      ( k2_xboole_0(A_283,B_284) = B_284
      | k4_xboole_0(A_283,B_284) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_759,c_18])).

tff(c_7813,plain,(
    ! [B_83,A_84] : k2_xboole_0(B_83,k2_xboole_0(A_84,B_83)) = k2_xboole_0(A_84,B_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_7740])).

tff(c_1336,plain,(
    ! [A_138,B_139] : k2_xboole_0(A_138,k4_xboole_0(B_139,A_138)) = k2_xboole_0(A_138,B_139) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_16437,plain,(
    ! [A_400,B_401] : k4_xboole_0(k2_xboole_0(A_400,B_401),k4_xboole_0(B_401,A_400)) = k4_xboole_0(A_400,k4_xboole_0(B_401,A_400)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1336,c_32])).

tff(c_16536,plain,(
    ! [A_84,B_83] : k4_xboole_0(k2_xboole_0(A_84,B_83),k4_xboole_0(k2_xboole_0(A_84,B_83),B_83)) = k4_xboole_0(B_83,k4_xboole_0(k2_xboole_0(A_84,B_83),B_83)) ),
    inference(superposition,[status(thm),theory(equality)],[c_7813,c_16437])).

tff(c_16743,plain,(
    ! [B_402,A_403] : k4_xboole_0(B_402,k4_xboole_0(A_403,B_402)) = B_402 ),
    inference(demodulation,[status(thm),theory(equality)],[c_831,c_32,c_4,c_38,c_16536])).

tff(c_11786,plain,(
    ! [A_19,B_20] : k4_xboole_0(A_19,k4_xboole_0(A_19,B_20)) = k3_subset_1(A_19,k4_xboole_0(A_19,B_20)) ),
    inference(resolution,[status(thm)],[c_26,c_11633])).

tff(c_11844,plain,(
    ! [A_19,B_20] : k3_subset_1(A_19,k4_xboole_0(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_11786])).

tff(c_16761,plain,(
    ! [B_402,A_403] : k3_xboole_0(B_402,k4_xboole_0(A_403,B_402)) = k3_subset_1(B_402,B_402) ),
    inference(superposition,[status(thm),theory(equality)],[c_16743,c_11844])).

tff(c_17024,plain,(
    ! [B_404,A_405] : k3_xboole_0(B_404,k4_xboole_0(A_405,B_404)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_11846,c_16761])).

tff(c_17227,plain,(
    ! [A_31,B_32] : k3_xboole_0(k4_xboole_0(A_31,B_32),k3_xboole_0(A_31,B_32)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_17024])).

tff(c_190143,plain,(
    k3_xboole_0(k2_tops_1('#skF_1','#skF_2'),k3_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_190127,c_17227])).

tff(c_190402,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_44715,c_190143])).

tff(c_190404,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_99809,c_190402])).

tff(c_190405,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_12070])).

tff(c_74,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_3323,plain,(
    ! [A_188,B_189] :
      ( v3_pre_topc(k1_tops_1(A_188,B_189),A_188)
      | ~ m1_subset_1(B_189,k1_zfmisc_1(u1_struct_0(A_188)))
      | ~ l1_pre_topc(A_188)
      | ~ v2_pre_topc(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_3331,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_3323])).

tff(c_3336,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_3331])).

tff(c_190428,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_190405,c_3336])).

tff(c_190446,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_190428])).

tff(c_190447,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_192808,plain,(
    ! [A_1354,B_1355,C_1356] :
      ( k7_subset_1(A_1354,B_1355,C_1356) = k4_xboole_0(B_1355,C_1356)
      | ~ m1_subset_1(B_1355,k1_zfmisc_1(A_1354)) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_192817,plain,(
    ! [C_1356] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_1356) = k4_xboole_0('#skF_2',C_1356) ),
    inference(resolution,[status(thm)],[c_70,c_192808])).

tff(c_194559,plain,(
    ! [A_1398,B_1399] :
      ( k7_subset_1(u1_struct_0(A_1398),B_1399,k2_tops_1(A_1398,B_1399)) = k1_tops_1(A_1398,B_1399)
      | ~ m1_subset_1(B_1399,k1_zfmisc_1(u1_struct_0(A_1398)))
      | ~ l1_pre_topc(A_1398) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_194572,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_194559])).

tff(c_194579,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_192817,c_194572])).

tff(c_194668,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_194579,c_26])).

tff(c_190448,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_194908,plain,(
    ! [B_1404,A_1405,C_1406] :
      ( r1_tarski(B_1404,k1_tops_1(A_1405,C_1406))
      | ~ r1_tarski(B_1404,C_1406)
      | ~ v3_pre_topc(B_1404,A_1405)
      | ~ m1_subset_1(C_1406,k1_zfmisc_1(u1_struct_0(A_1405)))
      | ~ m1_subset_1(B_1404,k1_zfmisc_1(u1_struct_0(A_1405)))
      | ~ l1_pre_topc(A_1405) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_194921,plain,(
    ! [B_1404] :
      ( r1_tarski(B_1404,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_1404,'#skF_2')
      | ~ v3_pre_topc(B_1404,'#skF_1')
      | ~ m1_subset_1(B_1404,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_70,c_194908])).

tff(c_197707,plain,(
    ! [B_1458] :
      ( r1_tarski(B_1458,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_1458,'#skF_2')
      | ~ v3_pre_topc(B_1458,'#skF_1')
      | ~ m1_subset_1(B_1458,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_194921])).

tff(c_197726,plain,
    ( r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_2'))
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_197707])).

tff(c_197735,plain,(
    r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_190448,c_10,c_197726])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( B_6 = A_5
      | ~ r1_tarski(B_6,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_197739,plain,
    ( k1_tops_1('#skF_1','#skF_2') = '#skF_2'
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_197735,c_6])).

tff(c_197752,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_194668,c_197739])).

tff(c_60,plain,(
    ! [A_54,B_56] :
      ( k7_subset_1(u1_struct_0(A_54),k2_pre_topc(A_54,B_56),k1_tops_1(A_54,B_56)) = k2_tops_1(A_54,B_56)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ l1_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_197782,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_197752,c_60])).

tff(c_197786,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_197782])).

tff(c_197788,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_190447,c_197786])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:30:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 49.39/40.05  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 49.39/40.07  
% 49.39/40.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 49.39/40.07  %$ v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 49.39/40.07  
% 49.39/40.07  %Foreground sorts:
% 49.39/40.07  
% 49.39/40.07  
% 49.39/40.07  %Background operators:
% 49.39/40.07  
% 49.39/40.07  
% 49.39/40.07  %Foreground operators:
% 49.39/40.07  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 49.39/40.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 49.39/40.07  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 49.39/40.07  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 49.39/40.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 49.39/40.07  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 49.39/40.07  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 49.39/40.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 49.39/40.07  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 49.39/40.07  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 49.39/40.07  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 49.39/40.07  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 49.39/40.07  tff('#skF_2', type, '#skF_2': $i).
% 49.39/40.07  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 49.39/40.07  tff('#skF_1', type, '#skF_1': $i).
% 49.39/40.07  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 49.39/40.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 49.39/40.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 49.39/40.07  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 49.39/40.07  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 49.39/40.07  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 49.39/40.07  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 49.39/40.07  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 49.39/40.07  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 49.39/40.07  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 49.39/40.07  
% 49.52/40.10  tff(f_171, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tops_1)).
% 49.52/40.10  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 49.52/40.10  tff(f_159, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 49.52/40.10  tff(f_73, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 49.52/40.10  tff(f_39, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 49.52/40.10  tff(f_59, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 49.52/40.10  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 49.52/40.10  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 49.52/40.10  tff(f_152, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 49.52/40.10  tff(f_109, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 49.52/40.10  tff(f_93, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 49.52/40.10  tff(f_71, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 49.52/40.10  tff(f_47, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 49.52/40.10  tff(f_61, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 49.52/40.10  tff(f_57, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 49.52/40.10  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 49.52/40.10  tff(f_103, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 49.52/40.10  tff(f_87, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 49.52/40.10  tff(f_77, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 49.52/40.10  tff(f_63, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 49.52/40.10  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 49.52/40.10  tff(f_65, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 49.52/40.10  tff(f_117, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 49.52/40.10  tff(f_138, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 49.52/40.10  tff(f_124, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 49.52/40.10  tff(c_76, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')!=k2_tops_1('#skF_1', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_171])).
% 49.52/40.10  tff(c_122, plain, (~v3_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_76])).
% 49.52/40.10  tff(c_72, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_171])).
% 49.52/40.10  tff(c_70, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_171])).
% 49.52/40.10  tff(c_2920, plain, (![A_178, B_179, C_180]: (k7_subset_1(A_178, B_179, C_180)=k4_xboole_0(B_179, C_180) | ~m1_subset_1(B_179, k1_zfmisc_1(A_178)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 49.52/40.10  tff(c_2929, plain, (![C_180]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_180)=k4_xboole_0('#skF_2', C_180))), inference(resolution, [status(thm)], [c_70, c_2920])).
% 49.52/40.10  tff(c_4192, plain, (![A_215, B_216]: (k7_subset_1(u1_struct_0(A_215), B_216, k2_tops_1(A_215, B_216))=k1_tops_1(A_215, B_216) | ~m1_subset_1(B_216, k1_zfmisc_1(u1_struct_0(A_215))) | ~l1_pre_topc(A_215))), inference(cnfTransformation, [status(thm)], [f_159])).
% 49.52/40.10  tff(c_4205, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_70, c_4192])).
% 49.52/40.10  tff(c_4212, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2929, c_4205])).
% 49.52/40.10  tff(c_38, plain, (![A_31, B_32]: (k4_xboole_0(A_31, k4_xboole_0(A_31, B_32))=k3_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_73])).
% 49.52/40.10  tff(c_4478, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4212, c_38])).
% 49.52/40.10  tff(c_12, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | k4_xboole_0(A_7, B_8)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 49.52/40.10  tff(c_26, plain, (![A_19, B_20]: (r1_tarski(k4_xboole_0(A_19, B_20), A_19))), inference(cnfTransformation, [status(thm)], [f_59])).
% 49.52/40.10  tff(c_1166, plain, (![B_132, A_133]: (B_132=A_133 | ~r1_tarski(B_132, A_133) | ~r1_tarski(A_133, B_132))), inference(cnfTransformation, [status(thm)], [f_35])).
% 49.52/40.10  tff(c_11968, plain, (![A_349, B_350]: (k4_xboole_0(A_349, B_350)=A_349 | ~r1_tarski(A_349, k4_xboole_0(A_349, B_350)))), inference(resolution, [status(thm)], [c_26, c_1166])).
% 49.52/40.10  tff(c_12004, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2' | ~r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4212, c_11968])).
% 49.52/40.10  tff(c_12070, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2' | ~r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4212, c_12004])).
% 49.52/40.10  tff(c_49487, plain, (~r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_12070])).
% 49.52/40.10  tff(c_49495, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_49487])).
% 49.52/40.10  tff(c_99809, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4478, c_49495])).
% 49.52/40.10  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 49.52/40.10  tff(c_4731, plain, (![A_221, B_222]: (k4_subset_1(u1_struct_0(A_221), B_222, k2_tops_1(A_221, B_222))=k2_pre_topc(A_221, B_222) | ~m1_subset_1(B_222, k1_zfmisc_1(u1_struct_0(A_221))) | ~l1_pre_topc(A_221))), inference(cnfTransformation, [status(thm)], [f_152])).
% 49.52/40.10  tff(c_4744, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_70, c_4731])).
% 49.52/40.10  tff(c_4751, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_4744])).
% 49.52/40.10  tff(c_56, plain, (![A_50, B_51]: (m1_subset_1(k2_tops_1(A_50, B_51), k1_zfmisc_1(u1_struct_0(A_50))) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_50))) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_109])).
% 49.52/40.10  tff(c_3638, plain, (![A_199, B_200, C_201]: (k4_subset_1(A_199, B_200, C_201)=k2_xboole_0(B_200, C_201) | ~m1_subset_1(C_201, k1_zfmisc_1(A_199)) | ~m1_subset_1(B_200, k1_zfmisc_1(A_199)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 49.52/40.10  tff(c_38572, plain, (![A_599, B_600, B_601]: (k4_subset_1(u1_struct_0(A_599), B_600, k2_tops_1(A_599, B_601))=k2_xboole_0(B_600, k2_tops_1(A_599, B_601)) | ~m1_subset_1(B_600, k1_zfmisc_1(u1_struct_0(A_599))) | ~m1_subset_1(B_601, k1_zfmisc_1(u1_struct_0(A_599))) | ~l1_pre_topc(A_599))), inference(resolution, [status(thm)], [c_56, c_3638])).
% 49.52/40.10  tff(c_38588, plain, (![B_601]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_601))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_601)) | ~m1_subset_1(B_601, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_70, c_38572])).
% 49.52/40.10  tff(c_43765, plain, (![B_648]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_648))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_648)) | ~m1_subset_1(B_648, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_38588])).
% 49.52/40.10  tff(c_43788, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_70, c_43765])).
% 49.52/40.10  tff(c_43797, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4751, c_43788])).
% 49.52/40.10  tff(c_36, plain, (![A_29, B_30]: (k4_xboole_0(A_29, k2_xboole_0(A_29, B_30))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_71])).
% 49.52/40.10  tff(c_43982, plain, (k4_xboole_0('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_43797, c_36])).
% 49.52/40.10  tff(c_20, plain, (![A_13]: (k2_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_47])).
% 49.52/40.10  tff(c_772, plain, (![A_115, B_116]: (k4_xboole_0(A_115, k4_xboole_0(A_115, B_116))=k3_xboole_0(A_115, B_116))), inference(cnfTransformation, [status(thm)], [f_73])).
% 49.52/40.10  tff(c_837, plain, (![A_117, B_118]: (r1_tarski(k3_xboole_0(A_117, B_118), A_117))), inference(superposition, [status(thm), theory('equality')], [c_772, c_26])).
% 49.52/40.10  tff(c_14, plain, (![A_7, B_8]: (k4_xboole_0(A_7, B_8)=k1_xboole_0 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 49.52/40.10  tff(c_1505, plain, (![A_142, B_143]: (k4_xboole_0(k3_xboole_0(A_142, B_143), A_142)=k1_xboole_0)), inference(resolution, [status(thm)], [c_837, c_14])).
% 49.52/40.10  tff(c_28, plain, (![A_21, B_22]: (k2_xboole_0(A_21, k4_xboole_0(B_22, A_21))=k2_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_61])).
% 49.52/40.10  tff(c_1510, plain, (![A_142, B_143]: (k2_xboole_0(A_142, k3_xboole_0(A_142, B_143))=k2_xboole_0(A_142, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1505, c_28])).
% 49.52/40.10  tff(c_1584, plain, (![A_144, B_145]: (k2_xboole_0(A_144, k3_xboole_0(A_144, B_145))=A_144)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1510])).
% 49.52/40.10  tff(c_1636, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k3_xboole_0(B_4, A_3))=A_3)), inference(superposition, [status(thm), theory('equality')], [c_4, c_1584])).
% 49.52/40.10  tff(c_650, plain, (![A_108, B_109]: (k3_xboole_0(A_108, B_109)=A_108 | ~r1_tarski(A_108, B_109))), inference(cnfTransformation, [status(thm)], [f_57])).
% 49.52/40.10  tff(c_6351, plain, (![A_258, B_259]: (k3_xboole_0(k4_xboole_0(A_258, B_259), A_258)=k4_xboole_0(A_258, B_259))), inference(resolution, [status(thm)], [c_26, c_650])).
% 49.52/40.10  tff(c_6412, plain, (![A_258, B_259]: (k3_xboole_0(A_258, k4_xboole_0(A_258, B_259))=k4_xboole_0(A_258, B_259))), inference(superposition, [status(thm), theory('equality')], [c_6351, c_4])).
% 49.52/40.10  tff(c_797, plain, (![A_31, B_32]: (k4_xboole_0(A_31, k3_xboole_0(A_31, B_32))=k3_xboole_0(A_31, k4_xboole_0(A_31, B_32)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_772])).
% 49.52/40.10  tff(c_18410, plain, (![A_412, B_413]: (k4_xboole_0(A_412, k3_xboole_0(A_412, B_413))=k4_xboole_0(A_412, B_413))), inference(demodulation, [status(thm), theory('equality')], [c_6412, c_797])).
% 49.52/40.10  tff(c_28684, plain, (![B_508, A_509]: (k4_xboole_0(B_508, k3_xboole_0(A_509, B_508))=k4_xboole_0(B_508, A_509))), inference(superposition, [status(thm), theory('equality')], [c_4, c_18410])).
% 49.52/40.10  tff(c_759, plain, (![A_113, B_114]: (r1_tarski(A_113, B_114) | k4_xboole_0(A_113, B_114)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 49.52/40.10  tff(c_18, plain, (![A_11, B_12]: (k2_xboole_0(A_11, B_12)=B_12 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 49.52/40.10  tff(c_770, plain, (![A_113, B_114]: (k2_xboole_0(A_113, B_114)=B_114 | k4_xboole_0(A_113, B_114)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_759, c_18])).
% 49.52/40.10  tff(c_28794, plain, (![B_508, A_509]: (k2_xboole_0(B_508, k3_xboole_0(A_509, B_508))=k3_xboole_0(A_509, B_508) | k4_xboole_0(B_508, A_509)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_28684, c_770])).
% 49.52/40.10  tff(c_29000, plain, (![A_509, B_508]: (k3_xboole_0(A_509, B_508)=B_508 | k4_xboole_0(B_508, A_509)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1636, c_28794])).
% 49.52/40.10  tff(c_44715, plain, (k3_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_43982, c_29000])).
% 49.52/40.10  tff(c_82, plain, (v3_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_171])).
% 49.52/40.10  tff(c_310, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_122, c_82])).
% 49.52/40.10  tff(c_54, plain, (![A_48, B_49]: (m1_subset_1(A_48, k1_zfmisc_1(B_49)) | ~r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_103])).
% 49.52/40.10  tff(c_13024, plain, (![B_360, A_361, C_362]: (k7_subset_1(B_360, A_361, C_362)=k4_xboole_0(A_361, C_362) | ~r1_tarski(A_361, B_360))), inference(resolution, [status(thm)], [c_54, c_2920])).
% 49.52/40.10  tff(c_110133, plain, (![B_958, A_959, C_960]: (k7_subset_1(B_958, A_959, C_960)=k4_xboole_0(A_959, C_960) | k4_xboole_0(A_959, B_958)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_13024])).
% 49.52/40.10  tff(c_110218, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2') | k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_310, c_110133])).
% 49.52/40.10  tff(c_110994, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_110218])).
% 49.52/40.10  tff(c_3471, plain, (![A_194, B_195, C_196]: (m1_subset_1(k4_subset_1(A_194, B_195, C_196), k1_zfmisc_1(A_194)) | ~m1_subset_1(C_196, k1_zfmisc_1(A_194)) | ~m1_subset_1(B_195, k1_zfmisc_1(A_194)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 49.52/40.10  tff(c_52, plain, (![A_48, B_49]: (r1_tarski(A_48, B_49) | ~m1_subset_1(A_48, k1_zfmisc_1(B_49)))), inference(cnfTransformation, [status(thm)], [f_103])).
% 49.52/40.10  tff(c_20364, plain, (![A_428, B_429, C_430]: (r1_tarski(k4_subset_1(A_428, B_429, C_430), A_428) | ~m1_subset_1(C_430, k1_zfmisc_1(A_428)) | ~m1_subset_1(B_429, k1_zfmisc_1(A_428)))), inference(resolution, [status(thm)], [c_3471, c_52])).
% 49.52/40.10  tff(c_20420, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_4751, c_20364])).
% 49.52/40.10  tff(c_20445, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_20420])).
% 49.52/40.10  tff(c_189681, plain, (~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_20445])).
% 49.52/40.10  tff(c_189684, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_56, c_189681])).
% 49.52/40.10  tff(c_189691, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_189684])).
% 49.52/40.10  tff(c_189692, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_20445])).
% 49.52/40.10  tff(c_189735, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))=k1_xboole_0), inference(resolution, [status(thm)], [c_189692, c_14])).
% 49.52/40.10  tff(c_189756, plain, $false, inference(negUnitSimplification, [status(thm)], [c_110994, c_189735])).
% 49.52/40.10  tff(c_189758, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_110218])).
% 49.52/40.10  tff(c_110179, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2') | k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_110133, c_310])).
% 49.52/40.10  tff(c_190127, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_189758, c_110179])).
% 49.52/40.10  tff(c_108, plain, (![A_79, B_80]: (k4_xboole_0(A_79, k2_xboole_0(A_79, B_80))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_71])).
% 49.52/40.10  tff(c_118, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_108])).
% 49.52/40.10  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 49.52/40.10  tff(c_2074, plain, (![A_161, B_162]: (k4_xboole_0(A_161, B_162)=k3_subset_1(A_161, B_162) | ~m1_subset_1(B_162, k1_zfmisc_1(A_161)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 49.52/40.10  tff(c_11633, plain, (![B_345, A_346]: (k4_xboole_0(B_345, A_346)=k3_subset_1(B_345, A_346) | ~r1_tarski(A_346, B_345))), inference(resolution, [status(thm)], [c_54, c_2074])).
% 49.52/40.10  tff(c_11789, plain, (![B_6]: (k4_xboole_0(B_6, B_6)=k3_subset_1(B_6, B_6))), inference(resolution, [status(thm)], [c_10, c_11633])).
% 49.52/40.10  tff(c_11846, plain, (![B_6]: (k3_subset_1(B_6, B_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_118, c_11789])).
% 49.52/40.10  tff(c_30, plain, (![A_23]: (k4_xboole_0(A_23, k1_xboole_0)=A_23)), inference(cnfTransformation, [status(thm)], [f_63])).
% 49.52/40.10  tff(c_144, plain, (![B_83, A_84]: (k2_xboole_0(B_83, A_84)=k2_xboole_0(A_84, B_83))), inference(cnfTransformation, [status(thm)], [f_27])).
% 49.52/40.10  tff(c_162, plain, (![B_83, A_84]: (k4_xboole_0(B_83, k2_xboole_0(A_84, B_83))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_144, c_36])).
% 49.52/40.10  tff(c_809, plain, (![B_83, A_84]: (k3_xboole_0(B_83, k2_xboole_0(A_84, B_83))=k4_xboole_0(B_83, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_162, c_772])).
% 49.52/40.10  tff(c_831, plain, (![B_83, A_84]: (k3_xboole_0(B_83, k2_xboole_0(A_84, B_83))=B_83)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_809])).
% 49.52/40.10  tff(c_32, plain, (![A_24, B_25]: (k4_xboole_0(k2_xboole_0(A_24, B_25), B_25)=k4_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_65])).
% 49.52/40.10  tff(c_7740, plain, (![A_283, B_284]: (k2_xboole_0(A_283, B_284)=B_284 | k4_xboole_0(A_283, B_284)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_759, c_18])).
% 49.52/40.10  tff(c_7813, plain, (![B_83, A_84]: (k2_xboole_0(B_83, k2_xboole_0(A_84, B_83))=k2_xboole_0(A_84, B_83))), inference(superposition, [status(thm), theory('equality')], [c_162, c_7740])).
% 49.52/40.10  tff(c_1336, plain, (![A_138, B_139]: (k2_xboole_0(A_138, k4_xboole_0(B_139, A_138))=k2_xboole_0(A_138, B_139))), inference(cnfTransformation, [status(thm)], [f_61])).
% 49.52/40.10  tff(c_16437, plain, (![A_400, B_401]: (k4_xboole_0(k2_xboole_0(A_400, B_401), k4_xboole_0(B_401, A_400))=k4_xboole_0(A_400, k4_xboole_0(B_401, A_400)))), inference(superposition, [status(thm), theory('equality')], [c_1336, c_32])).
% 49.52/40.10  tff(c_16536, plain, (![A_84, B_83]: (k4_xboole_0(k2_xboole_0(A_84, B_83), k4_xboole_0(k2_xboole_0(A_84, B_83), B_83))=k4_xboole_0(B_83, k4_xboole_0(k2_xboole_0(A_84, B_83), B_83)))), inference(superposition, [status(thm), theory('equality')], [c_7813, c_16437])).
% 49.52/40.10  tff(c_16743, plain, (![B_402, A_403]: (k4_xboole_0(B_402, k4_xboole_0(A_403, B_402))=B_402)), inference(demodulation, [status(thm), theory('equality')], [c_831, c_32, c_4, c_38, c_16536])).
% 49.52/40.10  tff(c_11786, plain, (![A_19, B_20]: (k4_xboole_0(A_19, k4_xboole_0(A_19, B_20))=k3_subset_1(A_19, k4_xboole_0(A_19, B_20)))), inference(resolution, [status(thm)], [c_26, c_11633])).
% 49.52/40.10  tff(c_11844, plain, (![A_19, B_20]: (k3_subset_1(A_19, k4_xboole_0(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_11786])).
% 49.52/40.10  tff(c_16761, plain, (![B_402, A_403]: (k3_xboole_0(B_402, k4_xboole_0(A_403, B_402))=k3_subset_1(B_402, B_402))), inference(superposition, [status(thm), theory('equality')], [c_16743, c_11844])).
% 49.52/40.10  tff(c_17024, plain, (![B_404, A_405]: (k3_xboole_0(B_404, k4_xboole_0(A_405, B_404))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_11846, c_16761])).
% 49.52/40.10  tff(c_17227, plain, (![A_31, B_32]: (k3_xboole_0(k4_xboole_0(A_31, B_32), k3_xboole_0(A_31, B_32))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_38, c_17024])).
% 49.52/40.10  tff(c_190143, plain, (k3_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k3_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_190127, c_17227])).
% 49.52/40.10  tff(c_190402, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4, c_44715, c_190143])).
% 49.52/40.10  tff(c_190404, plain, $false, inference(negUnitSimplification, [status(thm)], [c_99809, c_190402])).
% 49.52/40.10  tff(c_190405, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_12070])).
% 49.52/40.10  tff(c_74, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_171])).
% 49.52/40.10  tff(c_3323, plain, (![A_188, B_189]: (v3_pre_topc(k1_tops_1(A_188, B_189), A_188) | ~m1_subset_1(B_189, k1_zfmisc_1(u1_struct_0(A_188))) | ~l1_pre_topc(A_188) | ~v2_pre_topc(A_188))), inference(cnfTransformation, [status(thm)], [f_117])).
% 49.52/40.10  tff(c_3331, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_70, c_3323])).
% 49.52/40.10  tff(c_3336, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_3331])).
% 49.52/40.10  tff(c_190428, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_190405, c_3336])).
% 49.52/40.10  tff(c_190446, plain, $false, inference(negUnitSimplification, [status(thm)], [c_122, c_190428])).
% 49.52/40.10  tff(c_190447, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_76])).
% 49.52/40.10  tff(c_192808, plain, (![A_1354, B_1355, C_1356]: (k7_subset_1(A_1354, B_1355, C_1356)=k4_xboole_0(B_1355, C_1356) | ~m1_subset_1(B_1355, k1_zfmisc_1(A_1354)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 49.52/40.10  tff(c_192817, plain, (![C_1356]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_1356)=k4_xboole_0('#skF_2', C_1356))), inference(resolution, [status(thm)], [c_70, c_192808])).
% 49.52/40.10  tff(c_194559, plain, (![A_1398, B_1399]: (k7_subset_1(u1_struct_0(A_1398), B_1399, k2_tops_1(A_1398, B_1399))=k1_tops_1(A_1398, B_1399) | ~m1_subset_1(B_1399, k1_zfmisc_1(u1_struct_0(A_1398))) | ~l1_pre_topc(A_1398))), inference(cnfTransformation, [status(thm)], [f_159])).
% 49.52/40.10  tff(c_194572, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_70, c_194559])).
% 49.52/40.10  tff(c_194579, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_192817, c_194572])).
% 49.52/40.10  tff(c_194668, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_194579, c_26])).
% 49.52/40.10  tff(c_190448, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_76])).
% 49.52/40.10  tff(c_194908, plain, (![B_1404, A_1405, C_1406]: (r1_tarski(B_1404, k1_tops_1(A_1405, C_1406)) | ~r1_tarski(B_1404, C_1406) | ~v3_pre_topc(B_1404, A_1405) | ~m1_subset_1(C_1406, k1_zfmisc_1(u1_struct_0(A_1405))) | ~m1_subset_1(B_1404, k1_zfmisc_1(u1_struct_0(A_1405))) | ~l1_pre_topc(A_1405))), inference(cnfTransformation, [status(thm)], [f_138])).
% 49.52/40.10  tff(c_194921, plain, (![B_1404]: (r1_tarski(B_1404, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_1404, '#skF_2') | ~v3_pre_topc(B_1404, '#skF_1') | ~m1_subset_1(B_1404, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_70, c_194908])).
% 49.52/40.10  tff(c_197707, plain, (![B_1458]: (r1_tarski(B_1458, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_1458, '#skF_2') | ~v3_pre_topc(B_1458, '#skF_1') | ~m1_subset_1(B_1458, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_194921])).
% 49.52/40.10  tff(c_197726, plain, (r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_70, c_197707])).
% 49.52/40.10  tff(c_197735, plain, (r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_190448, c_10, c_197726])).
% 49.52/40.10  tff(c_6, plain, (![B_6, A_5]: (B_6=A_5 | ~r1_tarski(B_6, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 49.52/40.10  tff(c_197739, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2' | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_197735, c_6])).
% 49.52/40.10  tff(c_197752, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_194668, c_197739])).
% 49.52/40.10  tff(c_60, plain, (![A_54, B_56]: (k7_subset_1(u1_struct_0(A_54), k2_pre_topc(A_54, B_56), k1_tops_1(A_54, B_56))=k2_tops_1(A_54, B_56) | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0(A_54))) | ~l1_pre_topc(A_54))), inference(cnfTransformation, [status(thm)], [f_124])).
% 49.52/40.10  tff(c_197782, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_197752, c_60])).
% 49.52/40.10  tff(c_197786, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_197782])).
% 49.52/40.10  tff(c_197788, plain, $false, inference(negUnitSimplification, [status(thm)], [c_190447, c_197786])).
% 49.52/40.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 49.52/40.10  
% 49.52/40.10  Inference rules
% 49.52/40.10  ----------------------
% 49.52/40.10  #Ref     : 4
% 49.52/40.10  #Sup     : 50500
% 49.52/40.10  #Fact    : 0
% 49.52/40.10  #Define  : 0
% 49.52/40.10  #Split   : 11
% 49.52/40.10  #Chain   : 0
% 49.52/40.10  #Close   : 0
% 49.52/40.10  
% 49.52/40.10  Ordering : KBO
% 49.52/40.10  
% 49.52/40.10  Simplification rules
% 49.52/40.10  ----------------------
% 49.52/40.10  #Subsume      : 10624
% 49.52/40.10  #Demod        : 44892
% 49.52/40.10  #Tautology    : 24730
% 49.52/40.10  #SimpNegUnit  : 810
% 49.52/40.10  #BackRed      : 37
% 49.52/40.10  
% 49.52/40.10  #Partial instantiations: 0
% 49.52/40.10  #Strategies tried      : 1
% 49.52/40.10  
% 49.52/40.10  Timing (in seconds)
% 49.52/40.10  ----------------------
% 49.52/40.10  Preprocessing        : 0.38
% 49.52/40.10  Parsing              : 0.21
% 49.52/40.10  CNF conversion       : 0.02
% 49.52/40.10  Main loop            : 38.88
% 49.52/40.10  Inferencing          : 3.01
% 49.52/40.10  Reduction            : 25.05
% 49.52/40.10  Demodulation         : 22.54
% 49.52/40.10  BG Simplification    : 0.33
% 49.52/40.10  Subsumption          : 9.18
% 49.52/40.10  Abstraction          : 0.65
% 49.52/40.10  MUC search           : 0.00
% 49.52/40.10  Cooper               : 0.00
% 49.52/40.10  Total                : 39.32
% 49.52/40.10  Index Insertion      : 0.00
% 49.52/40.10  Index Deletion       : 0.00
% 49.52/40.10  Index Matching       : 0.00
% 49.52/40.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
