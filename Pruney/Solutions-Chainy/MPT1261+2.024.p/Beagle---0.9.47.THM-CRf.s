%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:14 EST 2020

% Result     : Theorem 8.40s
% Output     : CNFRefutation 8.59s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 243 expanded)
%              Number of leaves         :   48 ( 101 expanded)
%              Depth                    :   12
%              Number of atoms          :  210 ( 442 expanded)
%              Number of equality atoms :   87 ( 145 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_121,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_100,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_48,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_44,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_36,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_38,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_50,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_109,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_54,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_56,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_93,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_50,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_4440,plain,(
    ! [A_253,B_254,C_255] :
      ( k7_subset_1(A_253,B_254,C_255) = k4_xboole_0(B_254,C_255)
      | ~ m1_subset_1(B_254,k1_zfmisc_1(A_253)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4446,plain,(
    ! [C_255] : k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',C_255) = k4_xboole_0('#skF_3',C_255) ),
    inference(resolution,[status(thm)],[c_50,c_4440])).

tff(c_56,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k1_tops_1('#skF_2','#skF_3')) != k2_tops_1('#skF_2','#skF_3')
    | ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_112,plain,(
    ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_52,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1977,plain,(
    ! [A_140,B_141] :
      ( k4_subset_1(u1_struct_0(A_140),B_141,k2_tops_1(A_140,B_141)) = k2_pre_topc(A_140,B_141)
      | ~ m1_subset_1(B_141,k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ l1_pre_topc(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1984,plain,
    ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_1977])).

tff(c_1989,plain,(
    k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1984])).

tff(c_1023,plain,(
    ! [A_109,B_110,C_111] :
      ( k7_subset_1(A_109,B_110,C_111) = k4_xboole_0(B_110,C_111)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(A_109)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1030,plain,(
    ! [C_112] : k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',C_112) = k4_xboole_0('#skF_3',C_112) ),
    inference(resolution,[status(thm)],[c_50,c_1023])).

tff(c_62,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k1_tops_1('#skF_2','#skF_3')) = k2_tops_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_206,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k1_tops_1('#skF_2','#skF_3')) = k2_tops_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_62])).

tff(c_1036,plain,(
    k4_xboole_0('#skF_3',k1_tops_1('#skF_2','#skF_3')) = k2_tops_1('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1030,c_206])).

tff(c_20,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_16,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_522,plain,(
    ! [A_87,B_88] : k5_xboole_0(A_87,k3_xboole_0(A_87,B_88)) = k4_xboole_0(A_87,B_88) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_546,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = k4_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_522])).

tff(c_550,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_546])).

tff(c_12,plain,(
    ! [A_10] : k2_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_113,plain,(
    ! [A_56,B_57] : k4_xboole_0(A_56,k2_xboole_0(A_56,B_57)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_123,plain,(
    ! [A_10] : k4_xboole_0(A_10,A_10) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_113])).

tff(c_8,plain,(
    ! [A_6] : k3_xboole_0(A_6,A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_543,plain,(
    ! [A_6] : k5_xboole_0(A_6,A_6) = k4_xboole_0(A_6,A_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_522])).

tff(c_549,plain,(
    ! [A_6] : k5_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_543])).

tff(c_18,plain,(
    ! [A_14,B_15] : r1_tarski(k4_xboole_0(A_14,B_15),A_14) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_211,plain,(
    ! [A_68,B_69] :
      ( k3_xboole_0(A_68,B_69) = A_68
      | ~ r1_tarski(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_791,plain,(
    ! [A_98,B_99] : k3_xboole_0(k4_xboole_0(A_98,B_99),A_98) = k4_xboole_0(A_98,B_99) ),
    inference(resolution,[status(thm)],[c_18,c_211])).

tff(c_10,plain,(
    ! [A_8,B_9] : k5_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = k4_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_797,plain,(
    ! [A_98,B_99] : k5_xboole_0(k4_xboole_0(A_98,B_99),k4_xboole_0(A_98,B_99)) = k4_xboole_0(k4_xboole_0(A_98,B_99),A_98) ),
    inference(superposition,[status(thm),theory(equality)],[c_791,c_10])).

tff(c_852,plain,(
    ! [A_100,B_101] : k4_xboole_0(k4_xboole_0(A_100,B_101),A_100) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_549,c_797])).

tff(c_24,plain,(
    ! [A_19,B_20] : k5_xboole_0(A_19,k4_xboole_0(B_20,A_19)) = k2_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_863,plain,(
    ! [A_100,B_101] : k2_xboole_0(A_100,k4_xboole_0(A_100,B_101)) = k5_xboole_0(A_100,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_852,c_24])).

tff(c_901,plain,(
    ! [A_100,B_101] : k2_xboole_0(A_100,k4_xboole_0(A_100,B_101)) = A_100 ),
    inference(demodulation,[status(thm),theory(equality)],[c_550,c_863])).

tff(c_1051,plain,(
    k2_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1036,c_901])).

tff(c_1203,plain,(
    ! [A_117,B_118] :
      ( m1_subset_1(k2_tops_1(A_117,B_118),k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ l1_pre_topc(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_36,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(A_33,B_34)
      | ~ m1_subset_1(A_33,k1_zfmisc_1(B_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1213,plain,(
    ! [A_117,B_118] :
      ( r1_tarski(k2_tops_1(A_117,B_118),u1_struct_0(A_117))
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ l1_pre_topc(A_117) ) ),
    inference(resolution,[status(thm)],[c_1203,c_36])).

tff(c_38,plain,(
    ! [A_33,B_34] :
      ( m1_subset_1(A_33,k1_zfmisc_1(B_34))
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1767,plain,(
    ! [A_131,B_132,C_133] :
      ( k4_subset_1(A_131,B_132,C_133) = k2_xboole_0(B_132,C_133)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(A_131))
      | ~ m1_subset_1(B_132,k1_zfmisc_1(A_131)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2880,plain,(
    ! [B_169,B_170,A_171] :
      ( k4_subset_1(B_169,B_170,A_171) = k2_xboole_0(B_170,A_171)
      | ~ m1_subset_1(B_170,k1_zfmisc_1(B_169))
      | ~ r1_tarski(A_171,B_169) ) ),
    inference(resolution,[status(thm)],[c_38,c_1767])).

tff(c_2890,plain,(
    ! [A_172] :
      ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',A_172) = k2_xboole_0('#skF_3',A_172)
      | ~ r1_tarski(A_172,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_50,c_2880])).

tff(c_2894,plain,(
    ! [B_118] :
      ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2',B_118)) = k2_xboole_0('#skF_3',k2_tops_1('#skF_2',B_118))
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1213,c_2890])).

tff(c_3221,plain,(
    ! [B_192] :
      ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2',B_192)) = k2_xboole_0('#skF_3',k2_tops_1('#skF_2',B_192))
      | ~ m1_subset_1(B_192,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2894])).

tff(c_3232,plain,(
    k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_50,c_3221])).

tff(c_3238,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1989,c_1051,c_3232])).

tff(c_54,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1114,plain,(
    ! [A_113,B_114] :
      ( v4_pre_topc(k2_pre_topc(A_113,B_114),A_113)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ l1_pre_topc(A_113)
      | ~ v2_pre_topc(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1119,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_1114])).

tff(c_1123,plain,(
    v4_pre_topc(k2_pre_topc('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1119])).

tff(c_3240,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3238,c_1123])).

tff(c_3242,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_3240])).

tff(c_3243,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k1_tops_1('#skF_2','#skF_3')) != k2_tops_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_4532,plain,(
    k4_xboole_0('#skF_3',k1_tops_1('#skF_2','#skF_3')) != k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4446,c_3243])).

tff(c_3244,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_4822,plain,(
    ! [A_270,B_271] :
      ( r1_tarski(k2_tops_1(A_270,B_271),B_271)
      | ~ v4_pre_topc(B_271,A_270)
      | ~ m1_subset_1(B_271,k1_zfmisc_1(u1_struct_0(A_270)))
      | ~ l1_pre_topc(A_270) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_4829,plain,
    ( r1_tarski(k2_tops_1('#skF_2','#skF_3'),'#skF_3')
    | ~ v4_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_4822])).

tff(c_4834,plain,(
    r1_tarski(k2_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_3244,c_4829])).

tff(c_3313,plain,(
    ! [A_199,B_200] :
      ( r1_tarski(A_199,B_200)
      | ~ m1_subset_1(A_199,k1_zfmisc_1(B_200)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3317,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_50,c_3313])).

tff(c_26,plain,(
    ! [B_22,A_21] : k2_tarski(B_22,A_21) = k2_tarski(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_3386,plain,(
    ! [A_208,B_209] : k3_tarski(k2_tarski(A_208,B_209)) = k2_xboole_0(A_208,B_209) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_3494,plain,(
    ! [B_216,A_217] : k3_tarski(k2_tarski(B_216,A_217)) = k2_xboole_0(A_217,B_216) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_3386])).

tff(c_28,plain,(
    ! [A_23,B_24] : k3_tarski(k2_tarski(A_23,B_24)) = k2_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_3517,plain,(
    ! [B_218,A_219] : k2_xboole_0(B_218,A_219) = k2_xboole_0(A_219,B_218) ),
    inference(superposition,[status(thm),theory(equality)],[c_3494,c_28])).

tff(c_3570,plain,(
    ! [A_220] : k2_xboole_0(k1_xboole_0,A_220) = A_220 ),
    inference(superposition,[status(thm),theory(equality)],[c_3517,c_12])).

tff(c_22,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k2_xboole_0(A_17,B_18)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_3651,plain,(
    ! [A_224] : k4_xboole_0(k1_xboole_0,A_224) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3570,c_22])).

tff(c_3656,plain,(
    ! [A_224] : k5_xboole_0(A_224,k1_xboole_0) = k2_xboole_0(A_224,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3651,c_24])).

tff(c_3683,plain,(
    ! [A_224] : k5_xboole_0(A_224,k1_xboole_0) = A_224 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_3656])).

tff(c_3245,plain,(
    ! [A_193,B_194] : k4_xboole_0(A_193,k2_xboole_0(A_193,B_194)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_3255,plain,(
    ! [A_10] : k4_xboole_0(A_10,A_10) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_3245])).

tff(c_3804,plain,(
    ! [A_231,B_232] : k5_xboole_0(A_231,k3_xboole_0(A_231,B_232)) = k4_xboole_0(A_231,B_232) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_3833,plain,(
    ! [A_6] : k5_xboole_0(A_6,A_6) = k4_xboole_0(A_6,A_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_3804])).

tff(c_3842,plain,(
    ! [A_6] : k5_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3255,c_3833])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( k3_xboole_0(A_11,B_12) = A_11
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4838,plain,(
    k3_xboole_0(k2_tops_1('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_4834,c_14])).

tff(c_4845,plain,(
    k5_xboole_0(k2_tops_1('#skF_2','#skF_3'),k2_tops_1('#skF_2','#skF_3')) = k4_xboole_0(k2_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4838,c_10])).

tff(c_4860,plain,(
    k4_xboole_0(k2_tops_1('#skF_2','#skF_3'),'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3842,c_4845])).

tff(c_4880,plain,(
    k2_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = k5_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4860,c_24])).

tff(c_4891,plain,(
    k2_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3683,c_4880])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4125,plain,(
    ! [C_242,B_243,A_244] :
      ( r2_hidden(C_242,B_243)
      | ~ r2_hidden(C_242,A_244)
      | ~ r1_tarski(A_244,B_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5598,plain,(
    ! [A_291,B_292,B_293] :
      ( r2_hidden('#skF_1'(A_291,B_292),B_293)
      | ~ r1_tarski(A_291,B_293)
      | r1_tarski(A_291,B_292) ) ),
    inference(resolution,[status(thm)],[c_6,c_4125])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_6349,plain,(
    ! [A_330,B_331,B_332,B_333] :
      ( r2_hidden('#skF_1'(A_330,B_331),B_332)
      | ~ r1_tarski(B_333,B_332)
      | ~ r1_tarski(A_330,B_333)
      | r1_tarski(A_330,B_331) ) ),
    inference(resolution,[status(thm)],[c_5598,c_2])).

tff(c_6439,plain,(
    ! [A_343,B_344] :
      ( r2_hidden('#skF_1'(A_343,B_344),u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_343,'#skF_3')
      | r1_tarski(A_343,B_344) ) ),
    inference(resolution,[status(thm)],[c_3317,c_6349])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_6457,plain,(
    ! [A_346] :
      ( ~ r1_tarski(A_346,'#skF_3')
      | r1_tarski(A_346,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_6439,c_4])).

tff(c_4669,plain,(
    ! [A_265,B_266,C_267] :
      ( k4_subset_1(A_265,B_266,C_267) = k2_xboole_0(B_266,C_267)
      | ~ m1_subset_1(C_267,k1_zfmisc_1(A_265))
      | ~ m1_subset_1(B_266,k1_zfmisc_1(A_265)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_5938,plain,(
    ! [B_305,B_306,A_307] :
      ( k4_subset_1(B_305,B_306,A_307) = k2_xboole_0(B_306,A_307)
      | ~ m1_subset_1(B_306,k1_zfmisc_1(B_305))
      | ~ r1_tarski(A_307,B_305) ) ),
    inference(resolution,[status(thm)],[c_38,c_4669])).

tff(c_5947,plain,(
    ! [A_307] :
      ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',A_307) = k2_xboole_0('#skF_3',A_307)
      | ~ r1_tarski(A_307,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_50,c_5938])).

tff(c_6808,plain,(
    ! [A_354] :
      ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',A_354) = k2_xboole_0('#skF_3',A_354)
      | ~ r1_tarski(A_354,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_6457,c_5947])).

tff(c_5016,plain,(
    ! [A_273,B_274] :
      ( k4_subset_1(u1_struct_0(A_273),B_274,k2_tops_1(A_273,B_274)) = k2_pre_topc(A_273,B_274)
      | ~ m1_subset_1(B_274,k1_zfmisc_1(u1_struct_0(A_273)))
      | ~ l1_pre_topc(A_273) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_5025,plain,(
    ! [A_273,A_33] :
      ( k4_subset_1(u1_struct_0(A_273),A_33,k2_tops_1(A_273,A_33)) = k2_pre_topc(A_273,A_33)
      | ~ l1_pre_topc(A_273)
      | ~ r1_tarski(A_33,u1_struct_0(A_273)) ) ),
    inference(resolution,[status(thm)],[c_38,c_5016])).

tff(c_6825,plain,
    ( k2_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ r1_tarski('#skF_3',u1_struct_0('#skF_2'))
    | ~ r1_tarski(k2_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6808,c_5025])).

tff(c_6879,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4834,c_3317,c_52,c_4891,c_6825])).

tff(c_44,plain,(
    ! [A_39,B_41] :
      ( k7_subset_1(u1_struct_0(A_39),k2_pre_topc(A_39,B_41),k1_tops_1(A_39,B_41)) = k2_tops_1(A_39,B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_6912,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k1_tops_1('#skF_2','#skF_3')) = k2_tops_1('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6879,c_44])).

tff(c_6918,plain,(
    k4_xboole_0('#skF_3',k1_tops_1('#skF_2','#skF_3')) = k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_4446,c_6912])).

tff(c_6920,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4532,c_6918])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:39:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.40/3.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.47/3.29  
% 8.47/3.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.47/3.30  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 8.47/3.30  
% 8.47/3.30  %Foreground sorts:
% 8.47/3.30  
% 8.47/3.30  
% 8.47/3.30  %Background operators:
% 8.47/3.30  
% 8.47/3.30  
% 8.47/3.30  %Foreground operators:
% 8.47/3.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.47/3.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.47/3.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.47/3.30  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 8.47/3.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.47/3.30  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.47/3.30  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.47/3.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.47/3.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.47/3.30  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 8.47/3.30  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 8.47/3.30  tff('#skF_2', type, '#skF_2': $i).
% 8.47/3.30  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 8.47/3.30  tff('#skF_3', type, '#skF_3': $i).
% 8.47/3.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.47/3.30  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 8.47/3.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.47/3.30  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.47/3.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.47/3.30  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.47/3.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.47/3.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.47/3.30  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.47/3.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.47/3.30  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 8.47/3.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.47/3.30  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.47/3.30  
% 8.59/3.33  tff(f_121, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 8.59/3.33  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 8.59/3.33  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 8.59/3.33  tff(f_48, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 8.59/3.33  tff(f_44, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 8.59/3.33  tff(f_36, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.59/3.33  tff(f_38, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 8.59/3.33  tff(f_50, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 8.59/3.33  tff(f_34, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 8.59/3.33  tff(f_46, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 8.59/3.33  tff(f_42, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.59/3.33  tff(f_52, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 8.59/3.33  tff(f_78, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 8.59/3.33  tff(f_72, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 8.59/3.33  tff(f_62, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 8.59/3.33  tff(f_86, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_tops_1)).
% 8.59/3.33  tff(f_109, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_tops_1)).
% 8.59/3.33  tff(f_54, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 8.59/3.33  tff(f_56, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 8.59/3.33  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 8.59/3.33  tff(f_93, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 8.59/3.33  tff(c_50, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.59/3.33  tff(c_4440, plain, (![A_253, B_254, C_255]: (k7_subset_1(A_253, B_254, C_255)=k4_xboole_0(B_254, C_255) | ~m1_subset_1(B_254, k1_zfmisc_1(A_253)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 8.59/3.33  tff(c_4446, plain, (![C_255]: (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', C_255)=k4_xboole_0('#skF_3', C_255))), inference(resolution, [status(thm)], [c_50, c_4440])).
% 8.59/3.33  tff(c_56, plain, (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k1_tops_1('#skF_2', '#skF_3'))!=k2_tops_1('#skF_2', '#skF_3') | ~v4_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.59/3.33  tff(c_112, plain, (~v4_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_56])).
% 8.59/3.33  tff(c_52, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.59/3.33  tff(c_1977, plain, (![A_140, B_141]: (k4_subset_1(u1_struct_0(A_140), B_141, k2_tops_1(A_140, B_141))=k2_pre_topc(A_140, B_141) | ~m1_subset_1(B_141, k1_zfmisc_1(u1_struct_0(A_140))) | ~l1_pre_topc(A_140))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.59/3.33  tff(c_1984, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_50, c_1977])).
% 8.59/3.33  tff(c_1989, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1984])).
% 8.59/3.33  tff(c_1023, plain, (![A_109, B_110, C_111]: (k7_subset_1(A_109, B_110, C_111)=k4_xboole_0(B_110, C_111) | ~m1_subset_1(B_110, k1_zfmisc_1(A_109)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 8.59/3.33  tff(c_1030, plain, (![C_112]: (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', C_112)=k4_xboole_0('#skF_3', C_112))), inference(resolution, [status(thm)], [c_50, c_1023])).
% 8.59/3.33  tff(c_62, plain, (v4_pre_topc('#skF_3', '#skF_2') | k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k1_tops_1('#skF_2', '#skF_3'))=k2_tops_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.59/3.33  tff(c_206, plain, (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k1_tops_1('#skF_2', '#skF_3'))=k2_tops_1('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_112, c_62])).
% 8.59/3.33  tff(c_1036, plain, (k4_xboole_0('#skF_3', k1_tops_1('#skF_2', '#skF_3'))=k2_tops_1('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1030, c_206])).
% 8.59/3.33  tff(c_20, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_48])).
% 8.59/3.33  tff(c_16, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.59/3.33  tff(c_522, plain, (![A_87, B_88]: (k5_xboole_0(A_87, k3_xboole_0(A_87, B_88))=k4_xboole_0(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.59/3.33  tff(c_546, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=k4_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_522])).
% 8.59/3.33  tff(c_550, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_546])).
% 8.59/3.33  tff(c_12, plain, (![A_10]: (k2_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.59/3.33  tff(c_113, plain, (![A_56, B_57]: (k4_xboole_0(A_56, k2_xboole_0(A_56, B_57))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.59/3.33  tff(c_123, plain, (![A_10]: (k4_xboole_0(A_10, A_10)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_113])).
% 8.59/3.33  tff(c_8, plain, (![A_6]: (k3_xboole_0(A_6, A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.59/3.33  tff(c_543, plain, (![A_6]: (k5_xboole_0(A_6, A_6)=k4_xboole_0(A_6, A_6))), inference(superposition, [status(thm), theory('equality')], [c_8, c_522])).
% 8.59/3.33  tff(c_549, plain, (![A_6]: (k5_xboole_0(A_6, A_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_123, c_543])).
% 8.59/3.33  tff(c_18, plain, (![A_14, B_15]: (r1_tarski(k4_xboole_0(A_14, B_15), A_14))), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.59/3.33  tff(c_211, plain, (![A_68, B_69]: (k3_xboole_0(A_68, B_69)=A_68 | ~r1_tarski(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.59/3.33  tff(c_791, plain, (![A_98, B_99]: (k3_xboole_0(k4_xboole_0(A_98, B_99), A_98)=k4_xboole_0(A_98, B_99))), inference(resolution, [status(thm)], [c_18, c_211])).
% 8.59/3.33  tff(c_10, plain, (![A_8, B_9]: (k5_xboole_0(A_8, k3_xboole_0(A_8, B_9))=k4_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.59/3.33  tff(c_797, plain, (![A_98, B_99]: (k5_xboole_0(k4_xboole_0(A_98, B_99), k4_xboole_0(A_98, B_99))=k4_xboole_0(k4_xboole_0(A_98, B_99), A_98))), inference(superposition, [status(thm), theory('equality')], [c_791, c_10])).
% 8.59/3.33  tff(c_852, plain, (![A_100, B_101]: (k4_xboole_0(k4_xboole_0(A_100, B_101), A_100)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_549, c_797])).
% 8.59/3.33  tff(c_24, plain, (![A_19, B_20]: (k5_xboole_0(A_19, k4_xboole_0(B_20, A_19))=k2_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.59/3.33  tff(c_863, plain, (![A_100, B_101]: (k2_xboole_0(A_100, k4_xboole_0(A_100, B_101))=k5_xboole_0(A_100, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_852, c_24])).
% 8.59/3.33  tff(c_901, plain, (![A_100, B_101]: (k2_xboole_0(A_100, k4_xboole_0(A_100, B_101))=A_100)), inference(demodulation, [status(thm), theory('equality')], [c_550, c_863])).
% 8.59/3.33  tff(c_1051, plain, (k2_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1036, c_901])).
% 8.59/3.33  tff(c_1203, plain, (![A_117, B_118]: (m1_subset_1(k2_tops_1(A_117, B_118), k1_zfmisc_1(u1_struct_0(A_117))) | ~m1_subset_1(B_118, k1_zfmisc_1(u1_struct_0(A_117))) | ~l1_pre_topc(A_117))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.59/3.33  tff(c_36, plain, (![A_33, B_34]: (r1_tarski(A_33, B_34) | ~m1_subset_1(A_33, k1_zfmisc_1(B_34)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.59/3.33  tff(c_1213, plain, (![A_117, B_118]: (r1_tarski(k2_tops_1(A_117, B_118), u1_struct_0(A_117)) | ~m1_subset_1(B_118, k1_zfmisc_1(u1_struct_0(A_117))) | ~l1_pre_topc(A_117))), inference(resolution, [status(thm)], [c_1203, c_36])).
% 8.59/3.33  tff(c_38, plain, (![A_33, B_34]: (m1_subset_1(A_33, k1_zfmisc_1(B_34)) | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.59/3.33  tff(c_1767, plain, (![A_131, B_132, C_133]: (k4_subset_1(A_131, B_132, C_133)=k2_xboole_0(B_132, C_133) | ~m1_subset_1(C_133, k1_zfmisc_1(A_131)) | ~m1_subset_1(B_132, k1_zfmisc_1(A_131)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.59/3.33  tff(c_2880, plain, (![B_169, B_170, A_171]: (k4_subset_1(B_169, B_170, A_171)=k2_xboole_0(B_170, A_171) | ~m1_subset_1(B_170, k1_zfmisc_1(B_169)) | ~r1_tarski(A_171, B_169))), inference(resolution, [status(thm)], [c_38, c_1767])).
% 8.59/3.33  tff(c_2890, plain, (![A_172]: (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', A_172)=k2_xboole_0('#skF_3', A_172) | ~r1_tarski(A_172, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_50, c_2880])).
% 8.59/3.33  tff(c_2894, plain, (![B_118]: (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', B_118))=k2_xboole_0('#skF_3', k2_tops_1('#skF_2', B_118)) | ~m1_subset_1(B_118, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_1213, c_2890])).
% 8.59/3.33  tff(c_3221, plain, (![B_192]: (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', B_192))=k2_xboole_0('#skF_3', k2_tops_1('#skF_2', B_192)) | ~m1_subset_1(B_192, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_2894])).
% 8.59/3.33  tff(c_3232, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_50, c_3221])).
% 8.59/3.33  tff(c_3238, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1989, c_1051, c_3232])).
% 8.59/3.33  tff(c_54, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.59/3.33  tff(c_1114, plain, (![A_113, B_114]: (v4_pre_topc(k2_pre_topc(A_113, B_114), A_113) | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0(A_113))) | ~l1_pre_topc(A_113) | ~v2_pre_topc(A_113))), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.59/3.33  tff(c_1119, plain, (v4_pre_topc(k2_pre_topc('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_50, c_1114])).
% 8.59/3.33  tff(c_1123, plain, (v4_pre_topc(k2_pre_topc('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_1119])).
% 8.59/3.33  tff(c_3240, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3238, c_1123])).
% 8.59/3.33  tff(c_3242, plain, $false, inference(negUnitSimplification, [status(thm)], [c_112, c_3240])).
% 8.59/3.33  tff(c_3243, plain, (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k1_tops_1('#skF_2', '#skF_3'))!=k2_tops_1('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_56])).
% 8.59/3.33  tff(c_4532, plain, (k4_xboole_0('#skF_3', k1_tops_1('#skF_2', '#skF_3'))!=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4446, c_3243])).
% 8.59/3.33  tff(c_3244, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_56])).
% 8.59/3.33  tff(c_4822, plain, (![A_270, B_271]: (r1_tarski(k2_tops_1(A_270, B_271), B_271) | ~v4_pre_topc(B_271, A_270) | ~m1_subset_1(B_271, k1_zfmisc_1(u1_struct_0(A_270))) | ~l1_pre_topc(A_270))), inference(cnfTransformation, [status(thm)], [f_109])).
% 8.59/3.33  tff(c_4829, plain, (r1_tarski(k2_tops_1('#skF_2', '#skF_3'), '#skF_3') | ~v4_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_50, c_4822])).
% 8.59/3.33  tff(c_4834, plain, (r1_tarski(k2_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_3244, c_4829])).
% 8.59/3.33  tff(c_3313, plain, (![A_199, B_200]: (r1_tarski(A_199, B_200) | ~m1_subset_1(A_199, k1_zfmisc_1(B_200)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.59/3.33  tff(c_3317, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_50, c_3313])).
% 8.59/3.33  tff(c_26, plain, (![B_22, A_21]: (k2_tarski(B_22, A_21)=k2_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.59/3.33  tff(c_3386, plain, (![A_208, B_209]: (k3_tarski(k2_tarski(A_208, B_209))=k2_xboole_0(A_208, B_209))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.59/3.33  tff(c_3494, plain, (![B_216, A_217]: (k3_tarski(k2_tarski(B_216, A_217))=k2_xboole_0(A_217, B_216))), inference(superposition, [status(thm), theory('equality')], [c_26, c_3386])).
% 8.59/3.33  tff(c_28, plain, (![A_23, B_24]: (k3_tarski(k2_tarski(A_23, B_24))=k2_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.59/3.33  tff(c_3517, plain, (![B_218, A_219]: (k2_xboole_0(B_218, A_219)=k2_xboole_0(A_219, B_218))), inference(superposition, [status(thm), theory('equality')], [c_3494, c_28])).
% 8.59/3.33  tff(c_3570, plain, (![A_220]: (k2_xboole_0(k1_xboole_0, A_220)=A_220)), inference(superposition, [status(thm), theory('equality')], [c_3517, c_12])).
% 8.59/3.33  tff(c_22, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k2_xboole_0(A_17, B_18))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.59/3.33  tff(c_3651, plain, (![A_224]: (k4_xboole_0(k1_xboole_0, A_224)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3570, c_22])).
% 8.59/3.33  tff(c_3656, plain, (![A_224]: (k5_xboole_0(A_224, k1_xboole_0)=k2_xboole_0(A_224, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3651, c_24])).
% 8.59/3.33  tff(c_3683, plain, (![A_224]: (k5_xboole_0(A_224, k1_xboole_0)=A_224)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_3656])).
% 8.59/3.33  tff(c_3245, plain, (![A_193, B_194]: (k4_xboole_0(A_193, k2_xboole_0(A_193, B_194))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.59/3.33  tff(c_3255, plain, (![A_10]: (k4_xboole_0(A_10, A_10)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_3245])).
% 8.59/3.33  tff(c_3804, plain, (![A_231, B_232]: (k5_xboole_0(A_231, k3_xboole_0(A_231, B_232))=k4_xboole_0(A_231, B_232))), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.59/3.33  tff(c_3833, plain, (![A_6]: (k5_xboole_0(A_6, A_6)=k4_xboole_0(A_6, A_6))), inference(superposition, [status(thm), theory('equality')], [c_8, c_3804])).
% 8.59/3.33  tff(c_3842, plain, (![A_6]: (k5_xboole_0(A_6, A_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3255, c_3833])).
% 8.59/3.33  tff(c_14, plain, (![A_11, B_12]: (k3_xboole_0(A_11, B_12)=A_11 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.59/3.33  tff(c_4838, plain, (k3_xboole_0(k2_tops_1('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_4834, c_14])).
% 8.59/3.33  tff(c_4845, plain, (k5_xboole_0(k2_tops_1('#skF_2', '#skF_3'), k2_tops_1('#skF_2', '#skF_3'))=k4_xboole_0(k2_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4838, c_10])).
% 8.59/3.33  tff(c_4860, plain, (k4_xboole_0(k2_tops_1('#skF_2', '#skF_3'), '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3842, c_4845])).
% 8.59/3.33  tff(c_4880, plain, (k2_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k5_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4860, c_24])).
% 8.59/3.33  tff(c_4891, plain, (k2_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3683, c_4880])).
% 8.59/3.33  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.59/3.33  tff(c_4125, plain, (![C_242, B_243, A_244]: (r2_hidden(C_242, B_243) | ~r2_hidden(C_242, A_244) | ~r1_tarski(A_244, B_243))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.59/3.33  tff(c_5598, plain, (![A_291, B_292, B_293]: (r2_hidden('#skF_1'(A_291, B_292), B_293) | ~r1_tarski(A_291, B_293) | r1_tarski(A_291, B_292))), inference(resolution, [status(thm)], [c_6, c_4125])).
% 8.59/3.33  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.59/3.33  tff(c_6349, plain, (![A_330, B_331, B_332, B_333]: (r2_hidden('#skF_1'(A_330, B_331), B_332) | ~r1_tarski(B_333, B_332) | ~r1_tarski(A_330, B_333) | r1_tarski(A_330, B_331))), inference(resolution, [status(thm)], [c_5598, c_2])).
% 8.59/3.33  tff(c_6439, plain, (![A_343, B_344]: (r2_hidden('#skF_1'(A_343, B_344), u1_struct_0('#skF_2')) | ~r1_tarski(A_343, '#skF_3') | r1_tarski(A_343, B_344))), inference(resolution, [status(thm)], [c_3317, c_6349])).
% 8.59/3.33  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.59/3.33  tff(c_6457, plain, (![A_346]: (~r1_tarski(A_346, '#skF_3') | r1_tarski(A_346, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_6439, c_4])).
% 8.59/3.33  tff(c_4669, plain, (![A_265, B_266, C_267]: (k4_subset_1(A_265, B_266, C_267)=k2_xboole_0(B_266, C_267) | ~m1_subset_1(C_267, k1_zfmisc_1(A_265)) | ~m1_subset_1(B_266, k1_zfmisc_1(A_265)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.59/3.33  tff(c_5938, plain, (![B_305, B_306, A_307]: (k4_subset_1(B_305, B_306, A_307)=k2_xboole_0(B_306, A_307) | ~m1_subset_1(B_306, k1_zfmisc_1(B_305)) | ~r1_tarski(A_307, B_305))), inference(resolution, [status(thm)], [c_38, c_4669])).
% 8.59/3.33  tff(c_5947, plain, (![A_307]: (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', A_307)=k2_xboole_0('#skF_3', A_307) | ~r1_tarski(A_307, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_50, c_5938])).
% 8.59/3.33  tff(c_6808, plain, (![A_354]: (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', A_354)=k2_xboole_0('#skF_3', A_354) | ~r1_tarski(A_354, '#skF_3'))), inference(resolution, [status(thm)], [c_6457, c_5947])).
% 8.59/3.33  tff(c_5016, plain, (![A_273, B_274]: (k4_subset_1(u1_struct_0(A_273), B_274, k2_tops_1(A_273, B_274))=k2_pre_topc(A_273, B_274) | ~m1_subset_1(B_274, k1_zfmisc_1(u1_struct_0(A_273))) | ~l1_pre_topc(A_273))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.59/3.33  tff(c_5025, plain, (![A_273, A_33]: (k4_subset_1(u1_struct_0(A_273), A_33, k2_tops_1(A_273, A_33))=k2_pre_topc(A_273, A_33) | ~l1_pre_topc(A_273) | ~r1_tarski(A_33, u1_struct_0(A_273)))), inference(resolution, [status(thm)], [c_38, c_5016])).
% 8.59/3.33  tff(c_6825, plain, (k2_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2') | ~r1_tarski('#skF_3', u1_struct_0('#skF_2')) | ~r1_tarski(k2_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6808, c_5025])).
% 8.59/3.33  tff(c_6879, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4834, c_3317, c_52, c_4891, c_6825])).
% 8.59/3.33  tff(c_44, plain, (![A_39, B_41]: (k7_subset_1(u1_struct_0(A_39), k2_pre_topc(A_39, B_41), k1_tops_1(A_39, B_41))=k2_tops_1(A_39, B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(u1_struct_0(A_39))) | ~l1_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.59/3.33  tff(c_6912, plain, (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k1_tops_1('#skF_2', '#skF_3'))=k2_tops_1('#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6879, c_44])).
% 8.59/3.33  tff(c_6918, plain, (k4_xboole_0('#skF_3', k1_tops_1('#skF_2', '#skF_3'))=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_4446, c_6912])).
% 8.59/3.33  tff(c_6920, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4532, c_6918])).
% 8.59/3.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.59/3.33  
% 8.59/3.33  Inference rules
% 8.59/3.33  ----------------------
% 8.59/3.33  #Ref     : 0
% 8.59/3.33  #Sup     : 1656
% 8.59/3.33  #Fact    : 0
% 8.59/3.33  #Define  : 0
% 8.59/3.33  #Split   : 1
% 8.59/3.33  #Chain   : 0
% 8.59/3.33  #Close   : 0
% 8.59/3.33  
% 8.59/3.33  Ordering : KBO
% 8.59/3.33  
% 8.59/3.33  Simplification rules
% 8.59/3.33  ----------------------
% 8.59/3.33  #Subsume      : 66
% 8.59/3.33  #Demod        : 1933
% 8.59/3.33  #Tautology    : 1343
% 8.59/3.33  #SimpNegUnit  : 3
% 8.59/3.33  #BackRed      : 6
% 8.59/3.33  
% 8.59/3.33  #Partial instantiations: 0
% 8.59/3.33  #Strategies tried      : 1
% 8.59/3.33  
% 8.59/3.33  Timing (in seconds)
% 8.59/3.33  ----------------------
% 8.69/3.34  Preprocessing        : 0.56
% 8.69/3.34  Parsing              : 0.29
% 8.69/3.34  CNF conversion       : 0.04
% 8.69/3.34  Main loop            : 1.85
% 8.69/3.34  Inferencing          : 0.59
% 8.69/3.34  Reduction            : 0.83
% 8.69/3.34  Demodulation         : 0.69
% 8.69/3.34  BG Simplification    : 0.06
% 8.69/3.34  Subsumption          : 0.26
% 8.69/3.34  Abstraction          : 0.09
% 8.69/3.34  MUC search           : 0.00
% 8.69/3.34  Cooper               : 0.00
% 8.69/3.34  Total                : 2.49
% 8.69/3.34  Index Insertion      : 0.00
% 8.69/3.34  Index Deletion       : 0.00
% 8.69/3.34  Index Matching       : 0.00
% 8.69/3.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
