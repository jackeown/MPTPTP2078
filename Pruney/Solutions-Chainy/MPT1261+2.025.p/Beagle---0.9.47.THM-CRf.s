%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:15 EST 2020

% Result     : Theorem 25.12s
% Output     : CNFRefutation 25.12s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 529 expanded)
%              Number of leaves         :   51 ( 199 expanded)
%              Depth                    :   14
%              Number of atoms          :  216 ( 926 expanded)
%              Number of equality atoms :  103 ( 316 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_159,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_111,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_82,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_63,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_53,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_51,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,k2_xboole_0(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).

tff(f_131,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_124,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k2_tops_1(A,k3_subset_1(u1_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).

tff(f_117,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_140,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_147,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(c_76,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_47396,plain,(
    ! [A_929,B_930,C_931] :
      ( k7_subset_1(A_929,B_930,C_931) = k4_xboole_0(B_930,C_931)
      | ~ m1_subset_1(B_930,k1_zfmisc_1(A_929)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_47424,plain,(
    ! [C_931] : k7_subset_1(u1_struct_0('#skF_3'),'#skF_4',C_931) = k4_xboole_0('#skF_4',C_931) ),
    inference(resolution,[status(thm)],[c_76,c_47396])).

tff(c_82,plain,
    ( k7_subset_1(u1_struct_0('#skF_3'),'#skF_4',k1_tops_1('#skF_3','#skF_4')) != k2_tops_1('#skF_3','#skF_4')
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_237,plain,(
    ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_78,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_80,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_5847,plain,(
    ! [B_265,A_266] :
      ( v4_pre_topc(B_265,A_266)
      | k2_pre_topc(A_266,B_265) != B_265
      | ~ v2_pre_topc(A_266)
      | ~ m1_subset_1(B_265,k1_zfmisc_1(u1_struct_0(A_266)))
      | ~ l1_pre_topc(A_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_5887,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | k2_pre_topc('#skF_3','#skF_4') != '#skF_4'
    | ~ v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_5847])).

tff(c_5904,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | k2_pre_topc('#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_80,c_5887])).

tff(c_5905,plain,(
    k2_pre_topc('#skF_3','#skF_4') != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_237,c_5904])).

tff(c_1699,plain,(
    ! [A_184,B_185,C_186] :
      ( k7_subset_1(A_184,B_185,C_186) = k4_xboole_0(B_185,C_186)
      | ~ m1_subset_1(B_185,k1_zfmisc_1(A_184)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1754,plain,(
    ! [C_191] : k7_subset_1(u1_struct_0('#skF_3'),'#skF_4',C_191) = k4_xboole_0('#skF_4',C_191) ),
    inference(resolution,[status(thm)],[c_76,c_1699])).

tff(c_88,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | k7_subset_1(u1_struct_0('#skF_3'),'#skF_4',k1_tops_1('#skF_3','#skF_4')) = k2_tops_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_172,plain,(
    k7_subset_1(u1_struct_0('#skF_3'),'#skF_4',k1_tops_1('#skF_3','#skF_4')) = k2_tops_1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_1760,plain,(
    k4_xboole_0('#skF_4',k1_tops_1('#skF_3','#skF_4')) = k2_tops_1('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1754,c_172])).

tff(c_28,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_50,plain,(
    ! [A_37,B_38] : k6_subset_1(A_37,B_38) = k4_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_42,plain,(
    ! [A_26,B_27] : m1_subset_1(k6_subset_1(A_26,B_27),k1_zfmisc_1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_89,plain,(
    ! [A_26,B_27] : m1_subset_1(k4_xboole_0(A_26,B_27),k1_zfmisc_1(A_26)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_42])).

tff(c_663,plain,(
    ! [A_120,B_121] :
      ( k4_xboole_0(A_120,B_121) = k3_subset_1(A_120,B_121)
      | ~ m1_subset_1(B_121,k1_zfmisc_1(A_120)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_675,plain,(
    ! [A_26,B_27] : k4_xboole_0(A_26,k4_xboole_0(A_26,B_27)) = k3_subset_1(A_26,k4_xboole_0(A_26,B_27)) ),
    inference(resolution,[status(thm)],[c_89,c_663])).

tff(c_685,plain,(
    ! [A_26,B_27] : k3_subset_1(A_26,k4_xboole_0(A_26,B_27)) = k3_xboole_0(A_26,B_27) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_675])).

tff(c_1045,plain,(
    ! [A_154,B_155] :
      ( k3_subset_1(A_154,k3_subset_1(A_154,B_155)) = B_155
      | ~ m1_subset_1(B_155,k1_zfmisc_1(A_154)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1061,plain,(
    ! [A_26,B_27] : k3_subset_1(A_26,k3_subset_1(A_26,k4_xboole_0(A_26,B_27))) = k4_xboole_0(A_26,B_27) ),
    inference(resolution,[status(thm)],[c_89,c_1045])).

tff(c_1074,plain,(
    ! [A_26,B_27] : k3_subset_1(A_26,k3_xboole_0(A_26,B_27)) = k4_xboole_0(A_26,B_27) ),
    inference(demodulation,[status(thm),theory(equality)],[c_685,c_1061])).

tff(c_510,plain,(
    ! [A_110,B_111] : k4_xboole_0(A_110,k4_xboole_0(A_110,B_111)) = k3_xboole_0(A_110,B_111) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_735,plain,(
    ! [A_126,B_127] : m1_subset_1(k3_xboole_0(A_126,B_127),k1_zfmisc_1(A_126)) ),
    inference(superposition,[status(thm),theory(equality)],[c_510,c_89])).

tff(c_38,plain,(
    ! [A_22,B_23] :
      ( k4_xboole_0(A_22,B_23) = k3_subset_1(A_22,B_23)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(A_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_757,plain,(
    ! [A_126,B_127] : k4_xboole_0(A_126,k3_xboole_0(A_126,B_127)) = k3_subset_1(A_126,k3_xboole_0(A_126,B_127)) ),
    inference(resolution,[status(thm)],[c_735,c_38])).

tff(c_1921,plain,(
    ! [A_126,B_127] : k4_xboole_0(A_126,k3_xboole_0(A_126,B_127)) = k4_xboole_0(A_126,B_127) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1074,c_757])).

tff(c_513,plain,(
    ! [A_110,B_111] : k4_xboole_0(A_110,k3_xboole_0(A_110,B_111)) = k3_xboole_0(A_110,k4_xboole_0(A_110,B_111)) ),
    inference(superposition,[status(thm),theory(equality)],[c_510,c_28])).

tff(c_2002,plain,(
    ! [A_202,B_203] : k3_xboole_0(A_202,k4_xboole_0(A_202,B_203)) = k4_xboole_0(A_202,B_203) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1921,c_513])).

tff(c_2063,plain,(
    k4_xboole_0('#skF_4',k1_tops_1('#skF_3','#skF_4')) = k3_xboole_0('#skF_4',k2_tops_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1760,c_2002])).

tff(c_2098,plain,(
    k3_xboole_0('#skF_4',k2_tops_1('#skF_3','#skF_4')) = k2_tops_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1760,c_2063])).

tff(c_183,plain,(
    ! [A_77,B_78] :
      ( r1_tarski(A_77,B_78)
      | ~ m1_subset_1(A_77,k1_zfmisc_1(B_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_194,plain,(
    ! [A_26,B_27] : r1_tarski(k4_xboole_0(A_26,B_27),A_26) ),
    inference(resolution,[status(thm)],[c_89,c_183])).

tff(c_532,plain,(
    ! [A_110,B_111] : m1_subset_1(k3_xboole_0(A_110,B_111),k1_zfmisc_1(A_110)) ),
    inference(superposition,[status(thm),theory(equality)],[c_510,c_89])).

tff(c_60,plain,(
    ! [A_46,B_47] :
      ( m1_subset_1(A_46,k1_zfmisc_1(B_47))
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2753,plain,(
    ! [A_216,B_217,C_218] :
      ( k4_subset_1(A_216,B_217,C_218) = k2_xboole_0(B_217,C_218)
      | ~ m1_subset_1(C_218,k1_zfmisc_1(A_216))
      | ~ m1_subset_1(B_217,k1_zfmisc_1(A_216)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_9542,plain,(
    ! [B_323,B_324,A_325] :
      ( k4_subset_1(B_323,B_324,A_325) = k2_xboole_0(B_324,A_325)
      | ~ m1_subset_1(B_324,k1_zfmisc_1(B_323))
      | ~ r1_tarski(A_325,B_323) ) ),
    inference(resolution,[status(thm)],[c_60,c_2753])).

tff(c_44082,plain,(
    ! [A_791,B_792,A_793] :
      ( k4_subset_1(A_791,k3_xboole_0(A_791,B_792),A_793) = k2_xboole_0(k3_xboole_0(A_791,B_792),A_793)
      | ~ r1_tarski(A_793,A_791) ) ),
    inference(resolution,[status(thm)],[c_532,c_9542])).

tff(c_529,plain,(
    ! [A_110,B_111] : r1_tarski(k3_xboole_0(A_110,B_111),A_110) ),
    inference(superposition,[status(thm),theory(equality)],[c_510,c_194])).

tff(c_36,plain,(
    ! [A_21] : k2_subset_1(A_21) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_54,plain,(
    ! [A_42,B_43] :
      ( k4_subset_1(A_42,B_43,k3_subset_1(A_42,B_43)) = k2_subset_1(A_42)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1076,plain,(
    ! [A_156,B_157] :
      ( k4_subset_1(A_156,B_157,k3_subset_1(A_156,B_157)) = A_156
      | ~ m1_subset_1(B_157,k1_zfmisc_1(A_156)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_54])).

tff(c_1434,plain,(
    ! [B_173,A_174] :
      ( k4_subset_1(B_173,A_174,k3_subset_1(B_173,A_174)) = B_173
      | ~ r1_tarski(A_174,B_173) ) ),
    inference(resolution,[status(thm)],[c_60,c_1076])).

tff(c_1452,plain,(
    ! [A_26,B_27] :
      ( k4_subset_1(A_26,k3_xboole_0(A_26,B_27),k4_xboole_0(A_26,B_27)) = A_26
      | ~ r1_tarski(k3_xboole_0(A_26,B_27),A_26) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1074,c_1434])).

tff(c_1469,plain,(
    ! [A_26,B_27] : k4_subset_1(A_26,k3_xboole_0(A_26,B_27),k4_xboole_0(A_26,B_27)) = A_26 ),
    inference(demodulation,[status(thm),theory(equality)],[c_529,c_1452])).

tff(c_44137,plain,(
    ! [A_791,B_792] :
      ( k2_xboole_0(k3_xboole_0(A_791,B_792),k4_xboole_0(A_791,B_792)) = A_791
      | ~ r1_tarski(k4_xboole_0(A_791,B_792),A_791) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44082,c_1469])).

tff(c_44305,plain,(
    ! [A_791,B_792] : k2_xboole_0(k3_xboole_0(A_791,B_792),k4_xboole_0(A_791,B_792)) = A_791 ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_44137])).

tff(c_32,plain,(
    ! [B_18,A_17] : k2_tarski(B_18,A_17) = k2_tarski(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_197,plain,(
    ! [A_80,B_81] : k3_tarski(k2_tarski(A_80,B_81)) = k2_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_238,plain,(
    ! [B_88,A_89] : k3_tarski(k2_tarski(B_88,A_89)) = k2_xboole_0(A_89,B_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_197])).

tff(c_34,plain,(
    ! [A_19,B_20] : k3_tarski(k2_tarski(A_19,B_20)) = k2_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_244,plain,(
    ! [B_88,A_89] : k2_xboole_0(B_88,A_89) = k2_xboole_0(A_89,B_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_34])).

tff(c_44363,plain,(
    ! [A_794,B_795] : k2_xboole_0(k3_xboole_0(A_794,B_795),k4_xboole_0(A_794,B_795)) = A_794 ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_44137])).

tff(c_30,plain,(
    ! [A_15,B_16] : k2_xboole_0(A_15,k2_xboole_0(A_15,B_16)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_44390,plain,(
    ! [A_794,B_795] : k2_xboole_0(k3_xboole_0(A_794,B_795),k4_xboole_0(A_794,B_795)) = k2_xboole_0(k3_xboole_0(A_794,B_795),A_794) ),
    inference(superposition,[status(thm),theory(equality)],[c_44363,c_30])).

tff(c_44664,plain,(
    ! [A_796,B_797] : k2_xboole_0(A_796,k3_xboole_0(A_796,B_797)) = A_796 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44305,c_244,c_44390])).

tff(c_44765,plain,(
    k2_xboole_0('#skF_4',k2_tops_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2098,c_44664])).

tff(c_6015,plain,(
    ! [A_270,B_271] :
      ( k4_subset_1(u1_struct_0(A_270),B_271,k2_tops_1(A_270,B_271)) = k2_pre_topc(A_270,B_271)
      | ~ m1_subset_1(B_271,k1_zfmisc_1(u1_struct_0(A_270)))
      | ~ l1_pre_topc(A_270) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_6046,plain,
    ( k4_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_tops_1('#skF_3','#skF_4')) = k2_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_6015])).

tff(c_6064,plain,(
    k4_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_tops_1('#skF_3','#skF_4')) = k2_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_6046])).

tff(c_686,plain,(
    k4_xboole_0(u1_struct_0('#skF_3'),'#skF_4') = k3_subset_1(u1_struct_0('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_663])).

tff(c_829,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_686,c_89])).

tff(c_4202,plain,(
    ! [A_245,B_246] :
      ( k2_tops_1(A_245,k3_subset_1(u1_struct_0(A_245),B_246)) = k2_tops_1(A_245,B_246)
      | ~ m1_subset_1(B_246,k1_zfmisc_1(u1_struct_0(A_245)))
      | ~ l1_pre_topc(A_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_4229,plain,
    ( k2_tops_1('#skF_3',k3_subset_1(u1_struct_0('#skF_3'),'#skF_4')) = k2_tops_1('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_4202])).

tff(c_4248,plain,(
    k2_tops_1('#skF_3',k3_subset_1(u1_struct_0('#skF_3'),'#skF_4')) = k2_tops_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_4229])).

tff(c_66,plain,(
    ! [A_51,B_52] :
      ( m1_subset_1(k2_tops_1(A_51,B_52),k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_4392,plain,
    ( m1_subset_1(k2_tops_1('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4248,c_66])).

tff(c_4396,plain,(
    m1_subset_1(k2_tops_1('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_829,c_4392])).

tff(c_58,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(A_46,B_47)
      | ~ m1_subset_1(A_46,k1_zfmisc_1(B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_4438,plain,(
    r1_tarski(k2_tops_1('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_4396,c_58])).

tff(c_9779,plain,(
    ! [A_330] :
      ( k4_subset_1(u1_struct_0('#skF_3'),'#skF_4',A_330) = k2_xboole_0('#skF_4',A_330)
      | ~ r1_tarski(A_330,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_76,c_9542])).

tff(c_9790,plain,(
    k4_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_tops_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4',k2_tops_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_4438,c_9779])).

tff(c_9828,plain,(
    k2_xboole_0('#skF_4',k2_tops_1('#skF_3','#skF_4')) = k2_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6064,c_9790])).

tff(c_45347,plain,(
    k2_pre_topc('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44765,c_9828])).

tff(c_45349,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5905,c_45347])).

tff(c_45350,plain,(
    k7_subset_1(u1_struct_0('#skF_3'),'#skF_4',k1_tops_1('#skF_3','#skF_4')) != k2_tops_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_45559,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45350,c_172])).

tff(c_45560,plain,(
    v4_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_45612,plain,(
    k7_subset_1(u1_struct_0('#skF_3'),'#skF_4',k1_tops_1('#skF_3','#skF_4')) != k2_tops_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_45560,c_82])).

tff(c_47451,plain,(
    k4_xboole_0('#skF_4',k1_tops_1('#skF_3','#skF_4')) != k2_tops_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47424,c_45612])).

tff(c_49369,plain,(
    ! [A_972,B_973] :
      ( r1_tarski(k2_tops_1(A_972,B_973),B_973)
      | ~ v4_pre_topc(B_973,A_972)
      | ~ m1_subset_1(B_973,k1_zfmisc_1(u1_struct_0(A_972)))
      | ~ l1_pre_topc(A_972) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_49396,plain,
    ( r1_tarski(k2_tops_1('#skF_3','#skF_4'),'#skF_4')
    | ~ v4_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_49369])).

tff(c_49410,plain,(
    r1_tarski(k2_tops_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_45560,c_49396])).

tff(c_46267,plain,(
    ! [A_883,B_884] :
      ( k4_xboole_0(A_883,B_884) = k3_subset_1(A_883,B_884)
      | ~ m1_subset_1(B_884,k1_zfmisc_1(A_883)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_46297,plain,(
    ! [B_47,A_46] :
      ( k4_xboole_0(B_47,A_46) = k3_subset_1(B_47,A_46)
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(resolution,[status(thm)],[c_60,c_46267])).

tff(c_49414,plain,(
    k4_xboole_0('#skF_4',k2_tops_1('#skF_3','#skF_4')) = k3_subset_1('#skF_4',k2_tops_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_49410,c_46297])).

tff(c_51578,plain,(
    ! [A_1016,B_1017] :
      ( k7_subset_1(u1_struct_0(A_1016),B_1017,k2_tops_1(A_1016,B_1017)) = k1_tops_1(A_1016,B_1017)
      | ~ m1_subset_1(B_1017,k1_zfmisc_1(u1_struct_0(A_1016)))
      | ~ l1_pre_topc(A_1016) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_51609,plain,
    ( k7_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_tops_1('#skF_3','#skF_4')) = k1_tops_1('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_51578])).

tff(c_51629,plain,(
    k3_subset_1('#skF_4',k2_tops_1('#skF_3','#skF_4')) = k1_tops_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_49414,c_47424,c_51609])).

tff(c_46127,plain,(
    ! [A_871,B_872] :
      ( k3_subset_1(A_871,k3_subset_1(A_871,B_872)) = B_872
      | ~ m1_subset_1(B_872,k1_zfmisc_1(A_871)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_46148,plain,(
    ! [B_47,A_46] :
      ( k3_subset_1(B_47,k3_subset_1(B_47,A_46)) = A_46
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(resolution,[status(thm)],[c_60,c_46127])).

tff(c_51649,plain,
    ( k3_subset_1('#skF_4',k1_tops_1('#skF_3','#skF_4')) = k2_tops_1('#skF_3','#skF_4')
    | ~ r1_tarski(k2_tops_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_51629,c_46148])).

tff(c_51661,plain,(
    k3_subset_1('#skF_4',k1_tops_1('#skF_3','#skF_4')) = k2_tops_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49410,c_51649])).

tff(c_51642,plain,(
    k4_xboole_0('#skF_4',k2_tops_1('#skF_3','#skF_4')) = k1_tops_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51629,c_49414])).

tff(c_45572,plain,(
    ! [A_818,B_819] :
      ( r1_tarski(A_818,B_819)
      | ~ m1_subset_1(A_818,k1_zfmisc_1(B_819)) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_45583,plain,(
    ! [A_26,B_27] : r1_tarski(k4_xboole_0(A_26,B_27),A_26) ),
    inference(resolution,[status(thm)],[c_89,c_45572])).

tff(c_46288,plain,(
    ! [A_26,B_27] : k4_xboole_0(A_26,k4_xboole_0(A_26,B_27)) = k3_subset_1(A_26,k4_xboole_0(A_26,B_27)) ),
    inference(resolution,[status(thm)],[c_89,c_46267])).

tff(c_46301,plain,(
    ! [A_26,B_27] : k3_subset_1(A_26,k4_xboole_0(A_26,B_27)) = k3_xboole_0(A_26,B_27) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_46288])).

tff(c_46611,plain,(
    ! [B_900,A_901] :
      ( k3_subset_1(B_900,k3_subset_1(B_900,A_901)) = A_901
      | ~ r1_tarski(A_901,B_900) ) ),
    inference(resolution,[status(thm)],[c_60,c_46127])).

tff(c_46635,plain,(
    ! [A_26,B_27] :
      ( k3_subset_1(A_26,k3_xboole_0(A_26,B_27)) = k4_xboole_0(A_26,B_27)
      | ~ r1_tarski(k4_xboole_0(A_26,B_27),A_26) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46301,c_46611])).

tff(c_46656,plain,(
    ! [A_26,B_27] : k3_subset_1(A_26,k3_xboole_0(A_26,B_27)) = k4_xboole_0(A_26,B_27) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45583,c_46635])).

tff(c_46368,plain,(
    ! [A_887,B_888] : k3_subset_1(A_887,k4_xboole_0(A_887,B_888)) = k3_xboole_0(A_887,B_888) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_46288])).

tff(c_46386,plain,(
    ! [A_13,B_14] : k3_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_subset_1(A_13,k3_xboole_0(A_13,B_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_46368])).

tff(c_46906,plain,(
    ! [A_13,B_14] : k3_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k4_xboole_0(A_13,B_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46656,c_46386])).

tff(c_51779,plain,(
    k4_xboole_0('#skF_4',k2_tops_1('#skF_3','#skF_4')) = k3_xboole_0('#skF_4',k1_tops_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_51642,c_46906])).

tff(c_51810,plain,(
    k3_xboole_0('#skF_4',k1_tops_1('#skF_3','#skF_4')) = k1_tops_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51642,c_51779])).

tff(c_52024,plain,(
    k4_xboole_0('#skF_4',k1_tops_1('#skF_3','#skF_4')) = k3_subset_1('#skF_4',k1_tops_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_51810,c_46656])).

tff(c_52076,plain,(
    k4_xboole_0('#skF_4',k1_tops_1('#skF_3','#skF_4')) = k2_tops_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51661,c_52024])).

tff(c_52078,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47451,c_52076])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n002.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 10:53:07 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 25.12/13.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 25.12/13.20  
% 25.12/13.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 25.12/13.20  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 25.12/13.20  
% 25.12/13.20  %Foreground sorts:
% 25.12/13.20  
% 25.12/13.20  
% 25.12/13.20  %Background operators:
% 25.12/13.20  
% 25.12/13.20  
% 25.12/13.20  %Foreground operators:
% 25.12/13.20  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 25.12/13.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 25.12/13.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 25.12/13.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 25.12/13.20  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 25.12/13.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 25.12/13.20  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 25.12/13.20  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 25.12/13.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 25.12/13.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 25.12/13.20  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 25.12/13.20  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 25.12/13.20  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 25.12/13.20  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 25.12/13.20  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 25.12/13.20  tff('#skF_3', type, '#skF_3': $i).
% 25.12/13.20  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 25.12/13.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 25.12/13.20  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 25.12/13.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 25.12/13.20  tff(k3_tarski, type, k3_tarski: $i > $i).
% 25.12/13.20  tff('#skF_4', type, '#skF_4': $i).
% 25.12/13.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 25.12/13.20  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 25.12/13.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 25.12/13.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 25.12/13.20  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 25.12/13.20  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 25.12/13.20  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 25.12/13.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 25.12/13.20  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 25.12/13.20  
% 25.12/13.22  tff(f_159, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 25.12/13.22  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 25.12/13.22  tff(f_111, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 25.12/13.22  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 25.12/13.22  tff(f_82, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 25.12/13.22  tff(f_63, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 25.12/13.22  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 25.12/13.22  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 25.12/13.22  tff(f_96, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 25.12/13.22  tff(f_80, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 25.12/13.22  tff(f_53, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 25.12/13.22  tff(f_90, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 25.12/13.22  tff(f_49, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 25.12/13.22  tff(f_51, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 25.12/13.22  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, k2_xboole_0(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_1)).
% 25.12/13.22  tff(f_131, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 25.12/13.22  tff(f_124, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k2_tops_1(A, k3_subset_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_1)).
% 25.12/13.22  tff(f_117, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 25.12/13.22  tff(f_140, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 25.12/13.22  tff(f_147, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 25.12/13.22  tff(c_76, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_159])).
% 25.12/13.22  tff(c_47396, plain, (![A_929, B_930, C_931]: (k7_subset_1(A_929, B_930, C_931)=k4_xboole_0(B_930, C_931) | ~m1_subset_1(B_930, k1_zfmisc_1(A_929)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 25.12/13.22  tff(c_47424, plain, (![C_931]: (k7_subset_1(u1_struct_0('#skF_3'), '#skF_4', C_931)=k4_xboole_0('#skF_4', C_931))), inference(resolution, [status(thm)], [c_76, c_47396])).
% 25.12/13.22  tff(c_82, plain, (k7_subset_1(u1_struct_0('#skF_3'), '#skF_4', k1_tops_1('#skF_3', '#skF_4'))!=k2_tops_1('#skF_3', '#skF_4') | ~v4_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_159])).
% 25.12/13.22  tff(c_237, plain, (~v4_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_82])).
% 25.12/13.22  tff(c_78, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_159])).
% 25.12/13.22  tff(c_80, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_159])).
% 25.12/13.22  tff(c_5847, plain, (![B_265, A_266]: (v4_pre_topc(B_265, A_266) | k2_pre_topc(A_266, B_265)!=B_265 | ~v2_pre_topc(A_266) | ~m1_subset_1(B_265, k1_zfmisc_1(u1_struct_0(A_266))) | ~l1_pre_topc(A_266))), inference(cnfTransformation, [status(thm)], [f_111])).
% 25.12/13.22  tff(c_5887, plain, (v4_pre_topc('#skF_4', '#skF_3') | k2_pre_topc('#skF_3', '#skF_4')!='#skF_4' | ~v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_76, c_5847])).
% 25.12/13.22  tff(c_5904, plain, (v4_pre_topc('#skF_4', '#skF_3') | k2_pre_topc('#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_80, c_5887])).
% 25.12/13.22  tff(c_5905, plain, (k2_pre_topc('#skF_3', '#skF_4')!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_237, c_5904])).
% 25.12/13.22  tff(c_1699, plain, (![A_184, B_185, C_186]: (k7_subset_1(A_184, B_185, C_186)=k4_xboole_0(B_185, C_186) | ~m1_subset_1(B_185, k1_zfmisc_1(A_184)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 25.12/13.22  tff(c_1754, plain, (![C_191]: (k7_subset_1(u1_struct_0('#skF_3'), '#skF_4', C_191)=k4_xboole_0('#skF_4', C_191))), inference(resolution, [status(thm)], [c_76, c_1699])).
% 25.12/13.22  tff(c_88, plain, (v4_pre_topc('#skF_4', '#skF_3') | k7_subset_1(u1_struct_0('#skF_3'), '#skF_4', k1_tops_1('#skF_3', '#skF_4'))=k2_tops_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_159])).
% 25.12/13.22  tff(c_172, plain, (k7_subset_1(u1_struct_0('#skF_3'), '#skF_4', k1_tops_1('#skF_3', '#skF_4'))=k2_tops_1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_88])).
% 25.12/13.22  tff(c_1760, plain, (k4_xboole_0('#skF_4', k1_tops_1('#skF_3', '#skF_4'))=k2_tops_1('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1754, c_172])).
% 25.12/13.22  tff(c_28, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 25.12/13.22  tff(c_50, plain, (![A_37, B_38]: (k6_subset_1(A_37, B_38)=k4_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_82])).
% 25.12/13.22  tff(c_42, plain, (![A_26, B_27]: (m1_subset_1(k6_subset_1(A_26, B_27), k1_zfmisc_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 25.12/13.22  tff(c_89, plain, (![A_26, B_27]: (m1_subset_1(k4_xboole_0(A_26, B_27), k1_zfmisc_1(A_26)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_42])).
% 25.12/13.22  tff(c_663, plain, (![A_120, B_121]: (k4_xboole_0(A_120, B_121)=k3_subset_1(A_120, B_121) | ~m1_subset_1(B_121, k1_zfmisc_1(A_120)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 25.12/13.22  tff(c_675, plain, (![A_26, B_27]: (k4_xboole_0(A_26, k4_xboole_0(A_26, B_27))=k3_subset_1(A_26, k4_xboole_0(A_26, B_27)))), inference(resolution, [status(thm)], [c_89, c_663])).
% 25.12/13.22  tff(c_685, plain, (![A_26, B_27]: (k3_subset_1(A_26, k4_xboole_0(A_26, B_27))=k3_xboole_0(A_26, B_27))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_675])).
% 25.12/13.22  tff(c_1045, plain, (![A_154, B_155]: (k3_subset_1(A_154, k3_subset_1(A_154, B_155))=B_155 | ~m1_subset_1(B_155, k1_zfmisc_1(A_154)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 25.12/13.22  tff(c_1061, plain, (![A_26, B_27]: (k3_subset_1(A_26, k3_subset_1(A_26, k4_xboole_0(A_26, B_27)))=k4_xboole_0(A_26, B_27))), inference(resolution, [status(thm)], [c_89, c_1045])).
% 25.12/13.22  tff(c_1074, plain, (![A_26, B_27]: (k3_subset_1(A_26, k3_xboole_0(A_26, B_27))=k4_xboole_0(A_26, B_27))), inference(demodulation, [status(thm), theory('equality')], [c_685, c_1061])).
% 25.12/13.22  tff(c_510, plain, (![A_110, B_111]: (k4_xboole_0(A_110, k4_xboole_0(A_110, B_111))=k3_xboole_0(A_110, B_111))), inference(cnfTransformation, [status(thm)], [f_45])).
% 25.12/13.22  tff(c_735, plain, (![A_126, B_127]: (m1_subset_1(k3_xboole_0(A_126, B_127), k1_zfmisc_1(A_126)))), inference(superposition, [status(thm), theory('equality')], [c_510, c_89])).
% 25.12/13.22  tff(c_38, plain, (![A_22, B_23]: (k4_xboole_0(A_22, B_23)=k3_subset_1(A_22, B_23) | ~m1_subset_1(B_23, k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 25.12/13.22  tff(c_757, plain, (![A_126, B_127]: (k4_xboole_0(A_126, k3_xboole_0(A_126, B_127))=k3_subset_1(A_126, k3_xboole_0(A_126, B_127)))), inference(resolution, [status(thm)], [c_735, c_38])).
% 25.12/13.22  tff(c_1921, plain, (![A_126, B_127]: (k4_xboole_0(A_126, k3_xboole_0(A_126, B_127))=k4_xboole_0(A_126, B_127))), inference(demodulation, [status(thm), theory('equality')], [c_1074, c_757])).
% 25.12/13.22  tff(c_513, plain, (![A_110, B_111]: (k4_xboole_0(A_110, k3_xboole_0(A_110, B_111))=k3_xboole_0(A_110, k4_xboole_0(A_110, B_111)))), inference(superposition, [status(thm), theory('equality')], [c_510, c_28])).
% 25.12/13.22  tff(c_2002, plain, (![A_202, B_203]: (k3_xboole_0(A_202, k4_xboole_0(A_202, B_203))=k4_xboole_0(A_202, B_203))), inference(demodulation, [status(thm), theory('equality')], [c_1921, c_513])).
% 25.12/13.22  tff(c_2063, plain, (k4_xboole_0('#skF_4', k1_tops_1('#skF_3', '#skF_4'))=k3_xboole_0('#skF_4', k2_tops_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1760, c_2002])).
% 25.12/13.22  tff(c_2098, plain, (k3_xboole_0('#skF_4', k2_tops_1('#skF_3', '#skF_4'))=k2_tops_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1760, c_2063])).
% 25.12/13.22  tff(c_183, plain, (![A_77, B_78]: (r1_tarski(A_77, B_78) | ~m1_subset_1(A_77, k1_zfmisc_1(B_78)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 25.12/13.22  tff(c_194, plain, (![A_26, B_27]: (r1_tarski(k4_xboole_0(A_26, B_27), A_26))), inference(resolution, [status(thm)], [c_89, c_183])).
% 25.12/13.22  tff(c_532, plain, (![A_110, B_111]: (m1_subset_1(k3_xboole_0(A_110, B_111), k1_zfmisc_1(A_110)))), inference(superposition, [status(thm), theory('equality')], [c_510, c_89])).
% 25.12/13.22  tff(c_60, plain, (![A_46, B_47]: (m1_subset_1(A_46, k1_zfmisc_1(B_47)) | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_96])).
% 25.12/13.22  tff(c_2753, plain, (![A_216, B_217, C_218]: (k4_subset_1(A_216, B_217, C_218)=k2_xboole_0(B_217, C_218) | ~m1_subset_1(C_218, k1_zfmisc_1(A_216)) | ~m1_subset_1(B_217, k1_zfmisc_1(A_216)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 25.12/13.22  tff(c_9542, plain, (![B_323, B_324, A_325]: (k4_subset_1(B_323, B_324, A_325)=k2_xboole_0(B_324, A_325) | ~m1_subset_1(B_324, k1_zfmisc_1(B_323)) | ~r1_tarski(A_325, B_323))), inference(resolution, [status(thm)], [c_60, c_2753])).
% 25.12/13.22  tff(c_44082, plain, (![A_791, B_792, A_793]: (k4_subset_1(A_791, k3_xboole_0(A_791, B_792), A_793)=k2_xboole_0(k3_xboole_0(A_791, B_792), A_793) | ~r1_tarski(A_793, A_791))), inference(resolution, [status(thm)], [c_532, c_9542])).
% 25.12/13.22  tff(c_529, plain, (![A_110, B_111]: (r1_tarski(k3_xboole_0(A_110, B_111), A_110))), inference(superposition, [status(thm), theory('equality')], [c_510, c_194])).
% 25.12/13.22  tff(c_36, plain, (![A_21]: (k2_subset_1(A_21)=A_21)), inference(cnfTransformation, [status(thm)], [f_53])).
% 25.12/13.22  tff(c_54, plain, (![A_42, B_43]: (k4_subset_1(A_42, B_43, k3_subset_1(A_42, B_43))=k2_subset_1(A_42) | ~m1_subset_1(B_43, k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 25.12/13.22  tff(c_1076, plain, (![A_156, B_157]: (k4_subset_1(A_156, B_157, k3_subset_1(A_156, B_157))=A_156 | ~m1_subset_1(B_157, k1_zfmisc_1(A_156)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_54])).
% 25.12/13.22  tff(c_1434, plain, (![B_173, A_174]: (k4_subset_1(B_173, A_174, k3_subset_1(B_173, A_174))=B_173 | ~r1_tarski(A_174, B_173))), inference(resolution, [status(thm)], [c_60, c_1076])).
% 25.12/13.22  tff(c_1452, plain, (![A_26, B_27]: (k4_subset_1(A_26, k3_xboole_0(A_26, B_27), k4_xboole_0(A_26, B_27))=A_26 | ~r1_tarski(k3_xboole_0(A_26, B_27), A_26))), inference(superposition, [status(thm), theory('equality')], [c_1074, c_1434])).
% 25.12/13.22  tff(c_1469, plain, (![A_26, B_27]: (k4_subset_1(A_26, k3_xboole_0(A_26, B_27), k4_xboole_0(A_26, B_27))=A_26)), inference(demodulation, [status(thm), theory('equality')], [c_529, c_1452])).
% 25.12/13.22  tff(c_44137, plain, (![A_791, B_792]: (k2_xboole_0(k3_xboole_0(A_791, B_792), k4_xboole_0(A_791, B_792))=A_791 | ~r1_tarski(k4_xboole_0(A_791, B_792), A_791))), inference(superposition, [status(thm), theory('equality')], [c_44082, c_1469])).
% 25.12/13.22  tff(c_44305, plain, (![A_791, B_792]: (k2_xboole_0(k3_xboole_0(A_791, B_792), k4_xboole_0(A_791, B_792))=A_791)), inference(demodulation, [status(thm), theory('equality')], [c_194, c_44137])).
% 25.12/13.22  tff(c_32, plain, (![B_18, A_17]: (k2_tarski(B_18, A_17)=k2_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_49])).
% 25.12/13.22  tff(c_197, plain, (![A_80, B_81]: (k3_tarski(k2_tarski(A_80, B_81))=k2_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_51])).
% 25.12/13.22  tff(c_238, plain, (![B_88, A_89]: (k3_tarski(k2_tarski(B_88, A_89))=k2_xboole_0(A_89, B_88))), inference(superposition, [status(thm), theory('equality')], [c_32, c_197])).
% 25.12/13.22  tff(c_34, plain, (![A_19, B_20]: (k3_tarski(k2_tarski(A_19, B_20))=k2_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_51])).
% 25.12/13.22  tff(c_244, plain, (![B_88, A_89]: (k2_xboole_0(B_88, A_89)=k2_xboole_0(A_89, B_88))), inference(superposition, [status(thm), theory('equality')], [c_238, c_34])).
% 25.12/13.22  tff(c_44363, plain, (![A_794, B_795]: (k2_xboole_0(k3_xboole_0(A_794, B_795), k4_xboole_0(A_794, B_795))=A_794)), inference(demodulation, [status(thm), theory('equality')], [c_194, c_44137])).
% 25.12/13.22  tff(c_30, plain, (![A_15, B_16]: (k2_xboole_0(A_15, k2_xboole_0(A_15, B_16))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_47])).
% 25.12/13.22  tff(c_44390, plain, (![A_794, B_795]: (k2_xboole_0(k3_xboole_0(A_794, B_795), k4_xboole_0(A_794, B_795))=k2_xboole_0(k3_xboole_0(A_794, B_795), A_794))), inference(superposition, [status(thm), theory('equality')], [c_44363, c_30])).
% 25.12/13.22  tff(c_44664, plain, (![A_796, B_797]: (k2_xboole_0(A_796, k3_xboole_0(A_796, B_797))=A_796)), inference(demodulation, [status(thm), theory('equality')], [c_44305, c_244, c_44390])).
% 25.12/13.22  tff(c_44765, plain, (k2_xboole_0('#skF_4', k2_tops_1('#skF_3', '#skF_4'))='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_2098, c_44664])).
% 25.12/13.22  tff(c_6015, plain, (![A_270, B_271]: (k4_subset_1(u1_struct_0(A_270), B_271, k2_tops_1(A_270, B_271))=k2_pre_topc(A_270, B_271) | ~m1_subset_1(B_271, k1_zfmisc_1(u1_struct_0(A_270))) | ~l1_pre_topc(A_270))), inference(cnfTransformation, [status(thm)], [f_131])).
% 25.12/13.22  tff(c_6046, plain, (k4_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_tops_1('#skF_3', '#skF_4'))=k2_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_76, c_6015])).
% 25.12/13.22  tff(c_6064, plain, (k4_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_tops_1('#skF_3', '#skF_4'))=k2_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_6046])).
% 25.12/13.22  tff(c_686, plain, (k4_xboole_0(u1_struct_0('#skF_3'), '#skF_4')=k3_subset_1(u1_struct_0('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_76, c_663])).
% 25.12/13.22  tff(c_829, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_686, c_89])).
% 25.12/13.22  tff(c_4202, plain, (![A_245, B_246]: (k2_tops_1(A_245, k3_subset_1(u1_struct_0(A_245), B_246))=k2_tops_1(A_245, B_246) | ~m1_subset_1(B_246, k1_zfmisc_1(u1_struct_0(A_245))) | ~l1_pre_topc(A_245))), inference(cnfTransformation, [status(thm)], [f_124])).
% 25.12/13.22  tff(c_4229, plain, (k2_tops_1('#skF_3', k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'))=k2_tops_1('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_76, c_4202])).
% 25.12/13.22  tff(c_4248, plain, (k2_tops_1('#skF_3', k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'))=k2_tops_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_4229])).
% 25.12/13.22  tff(c_66, plain, (![A_51, B_52]: (m1_subset_1(k2_tops_1(A_51, B_52), k1_zfmisc_1(u1_struct_0(A_51))) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_117])).
% 25.12/13.22  tff(c_4392, plain, (m1_subset_1(k2_tops_1('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4248, c_66])).
% 25.12/13.22  tff(c_4396, plain, (m1_subset_1(k2_tops_1('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_829, c_4392])).
% 25.12/13.22  tff(c_58, plain, (![A_46, B_47]: (r1_tarski(A_46, B_47) | ~m1_subset_1(A_46, k1_zfmisc_1(B_47)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 25.12/13.22  tff(c_4438, plain, (r1_tarski(k2_tops_1('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_4396, c_58])).
% 25.12/13.22  tff(c_9779, plain, (![A_330]: (k4_subset_1(u1_struct_0('#skF_3'), '#skF_4', A_330)=k2_xboole_0('#skF_4', A_330) | ~r1_tarski(A_330, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_76, c_9542])).
% 25.12/13.22  tff(c_9790, plain, (k4_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_tops_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', k2_tops_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_4438, c_9779])).
% 25.12/13.22  tff(c_9828, plain, (k2_xboole_0('#skF_4', k2_tops_1('#skF_3', '#skF_4'))=k2_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6064, c_9790])).
% 25.12/13.22  tff(c_45347, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_44765, c_9828])).
% 25.12/13.22  tff(c_45349, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5905, c_45347])).
% 25.12/13.22  tff(c_45350, plain, (k7_subset_1(u1_struct_0('#skF_3'), '#skF_4', k1_tops_1('#skF_3', '#skF_4'))!=k2_tops_1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_82])).
% 25.12/13.22  tff(c_45559, plain, $false, inference(negUnitSimplification, [status(thm)], [c_45350, c_172])).
% 25.12/13.22  tff(c_45560, plain, (v4_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_88])).
% 25.12/13.22  tff(c_45612, plain, (k7_subset_1(u1_struct_0('#skF_3'), '#skF_4', k1_tops_1('#skF_3', '#skF_4'))!=k2_tops_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_45560, c_82])).
% 25.12/13.22  tff(c_47451, plain, (k4_xboole_0('#skF_4', k1_tops_1('#skF_3', '#skF_4'))!=k2_tops_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_47424, c_45612])).
% 25.12/13.22  tff(c_49369, plain, (![A_972, B_973]: (r1_tarski(k2_tops_1(A_972, B_973), B_973) | ~v4_pre_topc(B_973, A_972) | ~m1_subset_1(B_973, k1_zfmisc_1(u1_struct_0(A_972))) | ~l1_pre_topc(A_972))), inference(cnfTransformation, [status(thm)], [f_140])).
% 25.12/13.22  tff(c_49396, plain, (r1_tarski(k2_tops_1('#skF_3', '#skF_4'), '#skF_4') | ~v4_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_76, c_49369])).
% 25.12/13.22  tff(c_49410, plain, (r1_tarski(k2_tops_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_45560, c_49396])).
% 25.12/13.22  tff(c_46267, plain, (![A_883, B_884]: (k4_xboole_0(A_883, B_884)=k3_subset_1(A_883, B_884) | ~m1_subset_1(B_884, k1_zfmisc_1(A_883)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 25.12/13.22  tff(c_46297, plain, (![B_47, A_46]: (k4_xboole_0(B_47, A_46)=k3_subset_1(B_47, A_46) | ~r1_tarski(A_46, B_47))), inference(resolution, [status(thm)], [c_60, c_46267])).
% 25.12/13.22  tff(c_49414, plain, (k4_xboole_0('#skF_4', k2_tops_1('#skF_3', '#skF_4'))=k3_subset_1('#skF_4', k2_tops_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_49410, c_46297])).
% 25.12/13.22  tff(c_51578, plain, (![A_1016, B_1017]: (k7_subset_1(u1_struct_0(A_1016), B_1017, k2_tops_1(A_1016, B_1017))=k1_tops_1(A_1016, B_1017) | ~m1_subset_1(B_1017, k1_zfmisc_1(u1_struct_0(A_1016))) | ~l1_pre_topc(A_1016))), inference(cnfTransformation, [status(thm)], [f_147])).
% 25.12/13.22  tff(c_51609, plain, (k7_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_tops_1('#skF_3', '#skF_4'))=k1_tops_1('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_76, c_51578])).
% 25.12/13.22  tff(c_51629, plain, (k3_subset_1('#skF_4', k2_tops_1('#skF_3', '#skF_4'))=k1_tops_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_49414, c_47424, c_51609])).
% 25.12/13.22  tff(c_46127, plain, (![A_871, B_872]: (k3_subset_1(A_871, k3_subset_1(A_871, B_872))=B_872 | ~m1_subset_1(B_872, k1_zfmisc_1(A_871)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 25.12/13.22  tff(c_46148, plain, (![B_47, A_46]: (k3_subset_1(B_47, k3_subset_1(B_47, A_46))=A_46 | ~r1_tarski(A_46, B_47))), inference(resolution, [status(thm)], [c_60, c_46127])).
% 25.12/13.22  tff(c_51649, plain, (k3_subset_1('#skF_4', k1_tops_1('#skF_3', '#skF_4'))=k2_tops_1('#skF_3', '#skF_4') | ~r1_tarski(k2_tops_1('#skF_3', '#skF_4'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_51629, c_46148])).
% 25.12/13.22  tff(c_51661, plain, (k3_subset_1('#skF_4', k1_tops_1('#skF_3', '#skF_4'))=k2_tops_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_49410, c_51649])).
% 25.12/13.22  tff(c_51642, plain, (k4_xboole_0('#skF_4', k2_tops_1('#skF_3', '#skF_4'))=k1_tops_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_51629, c_49414])).
% 25.12/13.22  tff(c_45572, plain, (![A_818, B_819]: (r1_tarski(A_818, B_819) | ~m1_subset_1(A_818, k1_zfmisc_1(B_819)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 25.12/13.22  tff(c_45583, plain, (![A_26, B_27]: (r1_tarski(k4_xboole_0(A_26, B_27), A_26))), inference(resolution, [status(thm)], [c_89, c_45572])).
% 25.12/13.22  tff(c_46288, plain, (![A_26, B_27]: (k4_xboole_0(A_26, k4_xboole_0(A_26, B_27))=k3_subset_1(A_26, k4_xboole_0(A_26, B_27)))), inference(resolution, [status(thm)], [c_89, c_46267])).
% 25.12/13.22  tff(c_46301, plain, (![A_26, B_27]: (k3_subset_1(A_26, k4_xboole_0(A_26, B_27))=k3_xboole_0(A_26, B_27))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_46288])).
% 25.12/13.22  tff(c_46611, plain, (![B_900, A_901]: (k3_subset_1(B_900, k3_subset_1(B_900, A_901))=A_901 | ~r1_tarski(A_901, B_900))), inference(resolution, [status(thm)], [c_60, c_46127])).
% 25.12/13.22  tff(c_46635, plain, (![A_26, B_27]: (k3_subset_1(A_26, k3_xboole_0(A_26, B_27))=k4_xboole_0(A_26, B_27) | ~r1_tarski(k4_xboole_0(A_26, B_27), A_26))), inference(superposition, [status(thm), theory('equality')], [c_46301, c_46611])).
% 25.12/13.22  tff(c_46656, plain, (![A_26, B_27]: (k3_subset_1(A_26, k3_xboole_0(A_26, B_27))=k4_xboole_0(A_26, B_27))), inference(demodulation, [status(thm), theory('equality')], [c_45583, c_46635])).
% 25.12/13.22  tff(c_46368, plain, (![A_887, B_888]: (k3_subset_1(A_887, k4_xboole_0(A_887, B_888))=k3_xboole_0(A_887, B_888))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_46288])).
% 25.12/13.22  tff(c_46386, plain, (![A_13, B_14]: (k3_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_subset_1(A_13, k3_xboole_0(A_13, B_14)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_46368])).
% 25.12/13.22  tff(c_46906, plain, (![A_13, B_14]: (k3_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k4_xboole_0(A_13, B_14))), inference(demodulation, [status(thm), theory('equality')], [c_46656, c_46386])).
% 25.12/13.22  tff(c_51779, plain, (k4_xboole_0('#skF_4', k2_tops_1('#skF_3', '#skF_4'))=k3_xboole_0('#skF_4', k1_tops_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_51642, c_46906])).
% 25.12/13.22  tff(c_51810, plain, (k3_xboole_0('#skF_4', k1_tops_1('#skF_3', '#skF_4'))=k1_tops_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_51642, c_51779])).
% 25.12/13.22  tff(c_52024, plain, (k4_xboole_0('#skF_4', k1_tops_1('#skF_3', '#skF_4'))=k3_subset_1('#skF_4', k1_tops_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_51810, c_46656])).
% 25.12/13.22  tff(c_52076, plain, (k4_xboole_0('#skF_4', k1_tops_1('#skF_3', '#skF_4'))=k2_tops_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_51661, c_52024])).
% 25.12/13.22  tff(c_52078, plain, $false, inference(negUnitSimplification, [status(thm)], [c_47451, c_52076])).
% 25.12/13.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 25.12/13.22  
% 25.12/13.22  Inference rules
% 25.12/13.22  ----------------------
% 25.12/13.22  #Ref     : 0
% 25.12/13.22  #Sup     : 12615
% 25.12/13.22  #Fact    : 0
% 25.12/13.22  #Define  : 0
% 25.12/13.22  #Split   : 14
% 25.12/13.22  #Chain   : 0
% 25.12/13.22  #Close   : 0
% 25.12/13.22  
% 25.12/13.22  Ordering : KBO
% 25.12/13.22  
% 25.12/13.22  Simplification rules
% 25.12/13.22  ----------------------
% 25.12/13.22  #Subsume      : 1635
% 25.12/13.22  #Demod        : 17828
% 25.12/13.22  #Tautology    : 6694
% 25.12/13.22  #SimpNegUnit  : 158
% 25.12/13.22  #BackRed      : 265
% 25.12/13.22  
% 25.12/13.22  #Partial instantiations: 0
% 25.12/13.22  #Strategies tried      : 1
% 25.12/13.22  
% 25.12/13.22  Timing (in seconds)
% 25.12/13.22  ----------------------
% 25.12/13.23  Preprocessing        : 0.58
% 25.12/13.23  Parsing              : 0.30
% 25.12/13.23  CNF conversion       : 0.04
% 25.12/13.23  Main loop            : 11.70
% 25.12/13.23  Inferencing          : 2.00
% 25.12/13.23  Reduction            : 6.64
% 25.12/13.23  Demodulation         : 5.79
% 25.12/13.23  BG Simplification    : 0.22
% 25.12/13.23  Subsumption          : 2.25
% 25.12/13.23  Abstraction          : 0.39
% 25.12/13.23  MUC search           : 0.00
% 25.12/13.23  Cooper               : 0.00
% 25.12/13.23  Total                : 12.34
% 25.12/13.23  Index Insertion      : 0.00
% 25.12/13.23  Index Deletion       : 0.00
% 25.12/13.23  Index Matching       : 0.00
% 25.12/13.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
