%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:27 EST 2020

% Result     : Theorem 4.45s
% Output     : CNFRefutation 4.58s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 191 expanded)
%              Number of leaves         :   31 (  79 expanded)
%              Depth                    :   13
%              Number of atoms          :  137 ( 452 expanded)
%              Number of equality atoms :   27 (  85 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_104,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v4_pre_topc(B,A)
                    & v4_pre_topc(C,A) )
                 => k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,C)) = k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tops_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_89,axiom,(
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

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => r1_tarski(k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,C)),k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_pre_topc)).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_70,plain,(
    ! [A_41,B_42] :
      ( r1_tarski(A_41,B_42)
      | ~ m1_subset_1(A_41,k1_zfmisc_1(B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_78,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_56,c_70])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_113,plain,(
    ! [D_54,A_55,B_56] :
      ( r2_hidden(D_54,A_55)
      | ~ r2_hidden(D_54,k3_xboole_0(A_55,B_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_372,plain,(
    ! [A_93,B_94,B_95] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_93,B_94),B_95),A_93)
      | r1_tarski(k3_xboole_0(A_93,B_94),B_95) ) ),
    inference(resolution,[status(thm)],[c_6,c_113])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1452,plain,(
    ! [A_216,B_217,B_218,B_219] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_216,B_217),B_218),B_219)
      | ~ r1_tarski(A_216,B_219)
      | r1_tarski(k3_xboole_0(A_216,B_217),B_218) ) ),
    inference(resolution,[status(thm)],[c_372,c_2])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1470,plain,(
    ! [A_216,B_219,B_217] :
      ( ~ r1_tarski(A_216,B_219)
      | r1_tarski(k3_xboole_0(A_216,B_217),B_219) ) ),
    inference(resolution,[status(thm)],[c_1452,c_4])).

tff(c_30,plain,(
    ! [B_13] : r1_tarski(B_13,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_58,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_52,plain,(
    v4_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_279,plain,(
    ! [A_81,B_82] :
      ( k2_pre_topc(A_81,B_82) = B_82
      | ~ v4_pre_topc(B_82,A_81)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_pre_topc(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_289,plain,
    ( k2_pre_topc('#skF_4','#skF_5') = '#skF_5'
    | ~ v4_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_279])).

tff(c_296,plain,(
    k2_pre_topc('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_52,c_289])).

tff(c_160,plain,(
    ! [B_67,A_68] :
      ( r1_tarski(B_67,k2_pre_topc(A_68,B_67))
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_167,plain,
    ( r1_tarski('#skF_5',k2_pre_topc('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_160])).

tff(c_174,plain,(
    r1_tarski('#skF_5',k2_pre_topc('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_167])).

tff(c_26,plain,(
    ! [B_13,A_12] :
      ( B_13 = A_12
      | ~ r1_tarski(B_13,A_12)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_180,plain,
    ( k2_pre_topc('#skF_4','#skF_5') = '#skF_5'
    | ~ r1_tarski(k2_pre_topc('#skF_4','#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_174,c_26])).

tff(c_245,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_4','#skF_5'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_180])).

tff(c_299,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_296,c_245])).

tff(c_304,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_299])).

tff(c_305,plain,(
    k2_pre_topc('#skF_4','#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_180])).

tff(c_54,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_140,plain,(
    ! [A_63,B_64,C_65] :
      ( k9_subset_1(A_63,B_64,C_65) = k3_xboole_0(B_64,C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(A_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_148,plain,(
    ! [B_64] : k9_subset_1(u1_struct_0('#skF_4'),B_64,'#skF_6') = k3_xboole_0(B_64,'#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_140])).

tff(c_50,plain,(
    v4_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_210,plain,(
    ! [A_73,B_74] :
      ( k2_pre_topc(A_73,B_74) = B_74
      | ~ v4_pre_topc(B_74,A_73)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_217,plain,
    ( k2_pre_topc('#skF_4','#skF_6') = '#skF_6'
    | ~ v4_pre_topc('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_210])).

tff(c_224,plain,(
    k2_pre_topc('#skF_4','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_50,c_217])).

tff(c_165,plain,
    ( r1_tarski('#skF_6',k2_pre_topc('#skF_4','#skF_6'))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_160])).

tff(c_171,plain,(
    r1_tarski('#skF_6',k2_pre_topc('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_165])).

tff(c_177,plain,
    ( k2_pre_topc('#skF_4','#skF_6') = '#skF_6'
    | ~ r1_tarski(k2_pre_topc('#skF_4','#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_171,c_26])).

tff(c_190,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_4','#skF_6'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_177])).

tff(c_228,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_190])).

tff(c_233,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_228])).

tff(c_234,plain,(
    k2_pre_topc('#skF_4','#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_177])).

tff(c_48,plain,(
    k9_subset_1(u1_struct_0('#skF_4'),k2_pre_topc('#skF_4','#skF_5'),k2_pre_topc('#skF_4','#skF_6')) != k2_pre_topc('#skF_4',k9_subset_1(u1_struct_0('#skF_4'),'#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_150,plain,(
    k9_subset_1(u1_struct_0('#skF_4'),k2_pre_topc('#skF_4','#skF_5'),k2_pre_topc('#skF_4','#skF_6')) != k2_pre_topc('#skF_4',k3_xboole_0('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_48])).

tff(c_236,plain,(
    k9_subset_1(u1_struct_0('#skF_4'),k2_pre_topc('#skF_4','#skF_5'),'#skF_6') != k2_pre_topc('#skF_4',k3_xboole_0('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_150])).

tff(c_238,plain,(
    k3_xboole_0(k2_pre_topc('#skF_4','#skF_5'),'#skF_6') != k2_pre_topc('#skF_4',k3_xboole_0('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_236])).

tff(c_314,plain,(
    k2_pre_topc('#skF_4',k3_xboole_0('#skF_5','#skF_6')) != k3_xboole_0('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_305,c_238])).

tff(c_1737,plain,(
    ! [A_241,B_242,C_243] :
      ( r1_tarski(k2_pre_topc(A_241,k9_subset_1(u1_struct_0(A_241),B_242,C_243)),k9_subset_1(u1_struct_0(A_241),k2_pre_topc(A_241,B_242),k2_pre_topc(A_241,C_243)))
      | ~ m1_subset_1(C_243,k1_zfmisc_1(u1_struct_0(A_241)))
      | ~ m1_subset_1(B_242,k1_zfmisc_1(u1_struct_0(A_241)))
      | ~ l1_pre_topc(A_241) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1795,plain,(
    ! [B_64] :
      ( r1_tarski(k2_pre_topc('#skF_4',k3_xboole_0(B_64,'#skF_6')),k9_subset_1(u1_struct_0('#skF_4'),k2_pre_topc('#skF_4',B_64),k2_pre_topc('#skF_4','#skF_6')))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_1737])).

tff(c_2185,plain,(
    ! [B_260] :
      ( r1_tarski(k2_pre_topc('#skF_4',k3_xboole_0(B_260,'#skF_6')),k3_xboole_0(k2_pre_topc('#skF_4',B_260),'#skF_6'))
      | ~ m1_subset_1(B_260,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_148,c_234,c_1795])).

tff(c_2215,plain,
    ( r1_tarski(k2_pre_topc('#skF_4',k3_xboole_0('#skF_5','#skF_6')),k3_xboole_0('#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_305,c_2185])).

tff(c_2231,plain,(
    r1_tarski(k2_pre_topc('#skF_4',k3_xboole_0('#skF_5','#skF_6')),k3_xboole_0('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2215])).

tff(c_38,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(A_19,k1_zfmisc_1(B_20))
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_336,plain,(
    ! [A_88,A_89] :
      ( r1_tarski(A_88,k2_pre_topc(A_89,A_88))
      | ~ l1_pre_topc(A_89)
      | ~ r1_tarski(A_88,u1_struct_0(A_89)) ) ),
    inference(resolution,[status(thm)],[c_38,c_160])).

tff(c_348,plain,(
    ! [A_89,A_88] :
      ( k2_pre_topc(A_89,A_88) = A_88
      | ~ r1_tarski(k2_pre_topc(A_89,A_88),A_88)
      | ~ l1_pre_topc(A_89)
      | ~ r1_tarski(A_88,u1_struct_0(A_89)) ) ),
    inference(resolution,[status(thm)],[c_336,c_26])).

tff(c_2375,plain,
    ( k2_pre_topc('#skF_4',k3_xboole_0('#skF_5','#skF_6')) = k3_xboole_0('#skF_5','#skF_6')
    | ~ l1_pre_topc('#skF_4')
    | ~ r1_tarski(k3_xboole_0('#skF_5','#skF_6'),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_2231,c_348])).

tff(c_2398,plain,
    ( k2_pre_topc('#skF_4',k3_xboole_0('#skF_5','#skF_6')) = k3_xboole_0('#skF_5','#skF_6')
    | ~ r1_tarski(k3_xboole_0('#skF_5','#skF_6'),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2375])).

tff(c_2399,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_5','#skF_6'),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_314,c_2398])).

tff(c_2437,plain,(
    ~ r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1470,c_2399])).

tff(c_2450,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_2437])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:50:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.45/1.83  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.45/1.84  
% 4.45/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.45/1.84  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 4.45/1.84  
% 4.45/1.84  %Foreground sorts:
% 4.45/1.84  
% 4.45/1.84  
% 4.45/1.84  %Background operators:
% 4.45/1.84  
% 4.45/1.84  
% 4.45/1.84  %Foreground operators:
% 4.45/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.45/1.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.45/1.84  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.45/1.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.45/1.84  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.45/1.84  tff('#skF_5', type, '#skF_5': $i).
% 4.45/1.84  tff('#skF_6', type, '#skF_6': $i).
% 4.45/1.84  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.45/1.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.45/1.84  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.45/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.45/1.84  tff('#skF_4', type, '#skF_4': $i).
% 4.45/1.84  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.45/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.45/1.84  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.45/1.84  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.45/1.84  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.45/1.84  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.45/1.84  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.45/1.84  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.45/1.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.45/1.84  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.45/1.84  
% 4.58/1.86  tff(f_104, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & v4_pre_topc(C, A)) => (k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, C)) = k9_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_tops_1)).
% 4.58/1.86  tff(f_57, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.58/1.86  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.58/1.86  tff(f_41, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 4.58/1.86  tff(f_47, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.58/1.86  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 4.58/1.86  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 4.58/1.86  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 4.58/1.86  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, C)), k9_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_pre_topc)).
% 4.58/1.86  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.58/1.86  tff(c_70, plain, (![A_41, B_42]: (r1_tarski(A_41, B_42) | ~m1_subset_1(A_41, k1_zfmisc_1(B_42)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.58/1.86  tff(c_78, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_56, c_70])).
% 4.58/1.86  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.58/1.86  tff(c_113, plain, (![D_54, A_55, B_56]: (r2_hidden(D_54, A_55) | ~r2_hidden(D_54, k3_xboole_0(A_55, B_56)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.58/1.86  tff(c_372, plain, (![A_93, B_94, B_95]: (r2_hidden('#skF_1'(k3_xboole_0(A_93, B_94), B_95), A_93) | r1_tarski(k3_xboole_0(A_93, B_94), B_95))), inference(resolution, [status(thm)], [c_6, c_113])).
% 4.58/1.86  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.58/1.86  tff(c_1452, plain, (![A_216, B_217, B_218, B_219]: (r2_hidden('#skF_1'(k3_xboole_0(A_216, B_217), B_218), B_219) | ~r1_tarski(A_216, B_219) | r1_tarski(k3_xboole_0(A_216, B_217), B_218))), inference(resolution, [status(thm)], [c_372, c_2])).
% 4.58/1.86  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.58/1.86  tff(c_1470, plain, (![A_216, B_219, B_217]: (~r1_tarski(A_216, B_219) | r1_tarski(k3_xboole_0(A_216, B_217), B_219))), inference(resolution, [status(thm)], [c_1452, c_4])).
% 4.58/1.86  tff(c_30, plain, (![B_13]: (r1_tarski(B_13, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.58/1.86  tff(c_58, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.58/1.86  tff(c_52, plain, (v4_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.58/1.86  tff(c_279, plain, (![A_81, B_82]: (k2_pre_topc(A_81, B_82)=B_82 | ~v4_pre_topc(B_82, A_81) | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_pre_topc(A_81))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.58/1.86  tff(c_289, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5' | ~v4_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_56, c_279])).
% 4.58/1.86  tff(c_296, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_52, c_289])).
% 4.58/1.86  tff(c_160, plain, (![B_67, A_68]: (r1_tarski(B_67, k2_pre_topc(A_68, B_67)) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_pre_topc(A_68))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.58/1.86  tff(c_167, plain, (r1_tarski('#skF_5', k2_pre_topc('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_56, c_160])).
% 4.58/1.86  tff(c_174, plain, (r1_tarski('#skF_5', k2_pre_topc('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_167])).
% 4.58/1.86  tff(c_26, plain, (![B_13, A_12]: (B_13=A_12 | ~r1_tarski(B_13, A_12) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.58/1.86  tff(c_180, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5' | ~r1_tarski(k2_pre_topc('#skF_4', '#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_174, c_26])).
% 4.58/1.86  tff(c_245, plain, (~r1_tarski(k2_pre_topc('#skF_4', '#skF_5'), '#skF_5')), inference(splitLeft, [status(thm)], [c_180])).
% 4.58/1.86  tff(c_299, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_296, c_245])).
% 4.58/1.86  tff(c_304, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_299])).
% 4.58/1.86  tff(c_305, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_180])).
% 4.58/1.86  tff(c_54, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.58/1.86  tff(c_140, plain, (![A_63, B_64, C_65]: (k9_subset_1(A_63, B_64, C_65)=k3_xboole_0(B_64, C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(A_63)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.58/1.86  tff(c_148, plain, (![B_64]: (k9_subset_1(u1_struct_0('#skF_4'), B_64, '#skF_6')=k3_xboole_0(B_64, '#skF_6'))), inference(resolution, [status(thm)], [c_54, c_140])).
% 4.58/1.86  tff(c_50, plain, (v4_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.58/1.86  tff(c_210, plain, (![A_73, B_74]: (k2_pre_topc(A_73, B_74)=B_74 | ~v4_pre_topc(B_74, A_73) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_pre_topc(A_73))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.58/1.86  tff(c_217, plain, (k2_pre_topc('#skF_4', '#skF_6')='#skF_6' | ~v4_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_54, c_210])).
% 4.58/1.86  tff(c_224, plain, (k2_pre_topc('#skF_4', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_50, c_217])).
% 4.58/1.86  tff(c_165, plain, (r1_tarski('#skF_6', k2_pre_topc('#skF_4', '#skF_6')) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_54, c_160])).
% 4.58/1.86  tff(c_171, plain, (r1_tarski('#skF_6', k2_pre_topc('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_165])).
% 4.58/1.86  tff(c_177, plain, (k2_pre_topc('#skF_4', '#skF_6')='#skF_6' | ~r1_tarski(k2_pre_topc('#skF_4', '#skF_6'), '#skF_6')), inference(resolution, [status(thm)], [c_171, c_26])).
% 4.58/1.86  tff(c_190, plain, (~r1_tarski(k2_pre_topc('#skF_4', '#skF_6'), '#skF_6')), inference(splitLeft, [status(thm)], [c_177])).
% 4.58/1.86  tff(c_228, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_224, c_190])).
% 4.58/1.86  tff(c_233, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_228])).
% 4.58/1.86  tff(c_234, plain, (k2_pre_topc('#skF_4', '#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_177])).
% 4.58/1.86  tff(c_48, plain, (k9_subset_1(u1_struct_0('#skF_4'), k2_pre_topc('#skF_4', '#skF_5'), k2_pre_topc('#skF_4', '#skF_6'))!=k2_pre_topc('#skF_4', k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.58/1.86  tff(c_150, plain, (k9_subset_1(u1_struct_0('#skF_4'), k2_pre_topc('#skF_4', '#skF_5'), k2_pre_topc('#skF_4', '#skF_6'))!=k2_pre_topc('#skF_4', k3_xboole_0('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_48])).
% 4.58/1.86  tff(c_236, plain, (k9_subset_1(u1_struct_0('#skF_4'), k2_pre_topc('#skF_4', '#skF_5'), '#skF_6')!=k2_pre_topc('#skF_4', k3_xboole_0('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_234, c_150])).
% 4.58/1.86  tff(c_238, plain, (k3_xboole_0(k2_pre_topc('#skF_4', '#skF_5'), '#skF_6')!=k2_pre_topc('#skF_4', k3_xboole_0('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_236])).
% 4.58/1.86  tff(c_314, plain, (k2_pre_topc('#skF_4', k3_xboole_0('#skF_5', '#skF_6'))!=k3_xboole_0('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_305, c_238])).
% 4.58/1.86  tff(c_1737, plain, (![A_241, B_242, C_243]: (r1_tarski(k2_pre_topc(A_241, k9_subset_1(u1_struct_0(A_241), B_242, C_243)), k9_subset_1(u1_struct_0(A_241), k2_pre_topc(A_241, B_242), k2_pre_topc(A_241, C_243))) | ~m1_subset_1(C_243, k1_zfmisc_1(u1_struct_0(A_241))) | ~m1_subset_1(B_242, k1_zfmisc_1(u1_struct_0(A_241))) | ~l1_pre_topc(A_241))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.58/1.86  tff(c_1795, plain, (![B_64]: (r1_tarski(k2_pre_topc('#skF_4', k3_xboole_0(B_64, '#skF_6')), k9_subset_1(u1_struct_0('#skF_4'), k2_pre_topc('#skF_4', B_64), k2_pre_topc('#skF_4', '#skF_6'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_148, c_1737])).
% 4.58/1.86  tff(c_2185, plain, (![B_260]: (r1_tarski(k2_pre_topc('#skF_4', k3_xboole_0(B_260, '#skF_6')), k3_xboole_0(k2_pre_topc('#skF_4', B_260), '#skF_6')) | ~m1_subset_1(B_260, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_148, c_234, c_1795])).
% 4.58/1.86  tff(c_2215, plain, (r1_tarski(k2_pre_topc('#skF_4', k3_xboole_0('#skF_5', '#skF_6')), k3_xboole_0('#skF_5', '#skF_6')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_305, c_2185])).
% 4.58/1.86  tff(c_2231, plain, (r1_tarski(k2_pre_topc('#skF_4', k3_xboole_0('#skF_5', '#skF_6')), k3_xboole_0('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2215])).
% 4.58/1.86  tff(c_38, plain, (![A_19, B_20]: (m1_subset_1(A_19, k1_zfmisc_1(B_20)) | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.58/1.86  tff(c_336, plain, (![A_88, A_89]: (r1_tarski(A_88, k2_pre_topc(A_89, A_88)) | ~l1_pre_topc(A_89) | ~r1_tarski(A_88, u1_struct_0(A_89)))), inference(resolution, [status(thm)], [c_38, c_160])).
% 4.58/1.86  tff(c_348, plain, (![A_89, A_88]: (k2_pre_topc(A_89, A_88)=A_88 | ~r1_tarski(k2_pre_topc(A_89, A_88), A_88) | ~l1_pre_topc(A_89) | ~r1_tarski(A_88, u1_struct_0(A_89)))), inference(resolution, [status(thm)], [c_336, c_26])).
% 4.58/1.86  tff(c_2375, plain, (k2_pre_topc('#skF_4', k3_xboole_0('#skF_5', '#skF_6'))=k3_xboole_0('#skF_5', '#skF_6') | ~l1_pre_topc('#skF_4') | ~r1_tarski(k3_xboole_0('#skF_5', '#skF_6'), u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_2231, c_348])).
% 4.58/1.86  tff(c_2398, plain, (k2_pre_topc('#skF_4', k3_xboole_0('#skF_5', '#skF_6'))=k3_xboole_0('#skF_5', '#skF_6') | ~r1_tarski(k3_xboole_0('#skF_5', '#skF_6'), u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2375])).
% 4.58/1.86  tff(c_2399, plain, (~r1_tarski(k3_xboole_0('#skF_5', '#skF_6'), u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_314, c_2398])).
% 4.58/1.86  tff(c_2437, plain, (~r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_1470, c_2399])).
% 4.58/1.86  tff(c_2450, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_2437])).
% 4.58/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.58/1.86  
% 4.58/1.86  Inference rules
% 4.58/1.86  ----------------------
% 4.58/1.86  #Ref     : 0
% 4.58/1.86  #Sup     : 534
% 4.58/1.86  #Fact    : 0
% 4.58/1.86  #Define  : 0
% 4.58/1.86  #Split   : 7
% 4.58/1.86  #Chain   : 0
% 4.58/1.86  #Close   : 0
% 4.58/1.86  
% 4.58/1.86  Ordering : KBO
% 4.58/1.86  
% 4.58/1.86  Simplification rules
% 4.58/1.86  ----------------------
% 4.58/1.86  #Subsume      : 56
% 4.58/1.86  #Demod        : 217
% 4.58/1.86  #Tautology    : 164
% 4.58/1.86  #SimpNegUnit  : 4
% 4.58/1.86  #BackRed      : 14
% 4.58/1.86  
% 4.58/1.86  #Partial instantiations: 0
% 4.58/1.86  #Strategies tried      : 1
% 4.58/1.86  
% 4.58/1.86  Timing (in seconds)
% 4.58/1.86  ----------------------
% 4.58/1.86  Preprocessing        : 0.35
% 4.58/1.86  Parsing              : 0.18
% 4.58/1.86  CNF conversion       : 0.03
% 4.58/1.86  Main loop            : 0.68
% 4.58/1.86  Inferencing          : 0.24
% 4.58/1.86  Reduction            : 0.19
% 4.58/1.86  Demodulation         : 0.13
% 4.58/1.86  BG Simplification    : 0.03
% 4.58/1.86  Subsumption          : 0.17
% 4.58/1.86  Abstraction          : 0.04
% 4.58/1.86  MUC search           : 0.00
% 4.58/1.86  Cooper               : 0.00
% 4.58/1.86  Total                : 1.06
% 4.58/1.86  Index Insertion      : 0.00
% 4.58/1.86  Index Deletion       : 0.00
% 4.58/1.86  Index Matching       : 0.00
% 4.58/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
