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
% DateTime   : Thu Dec  3 10:14:54 EST 2020

% Result     : Theorem 4.53s
% Output     : CNFRefutation 4.62s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 376 expanded)
%              Number of leaves         :   46 ( 151 expanded)
%              Depth                    :   16
%              Number of atoms          :  132 ( 864 expanded)
%              Number of equality atoms :   54 ( 318 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_142,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_130,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_38,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(D,k1_enumset1(A,B,C))
    <=> ~ ( D != k1_xboole_0
          & D != k1_tarski(A)
          & D != k1_tarski(B)
          & D != k1_tarski(C)
          & D != k2_tarski(A,B)
          & D != k2_tarski(B,C)
          & D != k2_tarski(A,C)
          & D != k1_enumset1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_zfmisc_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_100,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

tff(f_112,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_80,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_131,plain,(
    ! [C_65,A_66,B_67] :
      ( v1_relat_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_135,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_131])).

tff(c_78,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_82,plain,(
    v1_funct_2('#skF_6',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_257,plain,(
    ! [A_110,B_111,C_112] :
      ( k1_relset_1(A_110,B_111,C_112) = k1_relat_1(C_112)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_261,plain,(
    k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_257])).

tff(c_296,plain,(
    ! [B_139,A_140,C_141] :
      ( k1_xboole_0 = B_139
      | k1_relset_1(A_140,B_139,C_141) = A_140
      | ~ v1_funct_2(C_141,A_140,B_139)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_140,B_139))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_299,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6') = k1_tarski('#skF_3')
    | ~ v1_funct_2('#skF_6',k1_tarski('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_296])).

tff(c_302,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_tarski('#skF_3') = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_261,c_299])).

tff(c_303,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_302])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_108,plain,(
    ! [A_61,B_62] : k1_enumset1(A_61,A_61,B_62) = k2_tarski(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_36,plain,(
    ! [C_15,A_13,B_14] : r1_tarski(k1_tarski(C_15),k1_enumset1(A_13,B_14,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_137,plain,(
    ! [B_69,A_70] : r1_tarski(k1_tarski(B_69),k2_tarski(A_70,B_69)) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_36])).

tff(c_140,plain,(
    ! [A_7] : r1_tarski(k1_tarski(A_7),k1_tarski(A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_137])).

tff(c_323,plain,(
    r1_tarski(k1_tarski('#skF_3'),k1_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_303,c_140])).

tff(c_344,plain,(
    r1_tarski(k1_relat_1('#skF_6'),k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_303,c_323])).

tff(c_46,plain,(
    ! [B_21,A_20] :
      ( v4_relat_1(B_21,A_20)
      | ~ r1_tarski(k1_relat_1(B_21),A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_355,plain,
    ( v4_relat_1('#skF_6',k1_relat_1('#skF_6'))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_344,c_46])).

tff(c_358,plain,(
    v4_relat_1('#skF_6',k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_355])).

tff(c_54,plain,(
    ! [B_27,A_26] :
      ( k7_relat_1(B_27,A_26) = B_27
      | ~ v4_relat_1(B_27,A_26)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_386,plain,
    ( k7_relat_1('#skF_6',k1_relat_1('#skF_6')) = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_358,c_54])).

tff(c_389,plain,(
    k7_relat_1('#skF_6',k1_relat_1('#skF_6')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_386])).

tff(c_52,plain,(
    ! [B_25,A_24] :
      ( k2_relat_1(k7_relat_1(B_25,A_24)) = k9_relat_1(B_25,A_24)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_397,plain,
    ( k9_relat_1('#skF_6',k1_relat_1('#skF_6')) = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_389,c_52])).

tff(c_403,plain,(
    k9_relat_1('#skF_6',k1_relat_1('#skF_6')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_397])).

tff(c_236,plain,(
    ! [B_104,A_105] :
      ( k2_relat_1(k7_relat_1(B_104,A_105)) = k9_relat_1(B_104,A_105)
      | ~ v1_relat_1(B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_50,plain,(
    ! [B_23,A_22] :
      ( r1_tarski(k9_relat_1(B_23,A_22),k2_relat_1(B_23))
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_242,plain,(
    ! [B_104,A_105,A_22] :
      ( r1_tarski(k9_relat_1(k7_relat_1(B_104,A_105),A_22),k9_relat_1(B_104,A_105))
      | ~ v1_relat_1(k7_relat_1(B_104,A_105))
      | ~ v1_relat_1(B_104) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_50])).

tff(c_1984,plain,(
    ! [A_22] :
      ( r1_tarski(k9_relat_1(k7_relat_1('#skF_6',k1_relat_1('#skF_6')),A_22),k2_relat_1('#skF_6'))
      | ~ v1_relat_1(k7_relat_1('#skF_6',k1_relat_1('#skF_6')))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_403,c_242])).

tff(c_1992,plain,(
    ! [A_22] : r1_tarski(k9_relat_1('#skF_6',A_22),k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_135,c_389,c_389,c_1984])).

tff(c_44,plain,(
    ! [A_17,B_19] :
      ( k9_relat_1(A_17,k1_tarski(B_19)) = k11_relat_1(A_17,B_19)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_4629,plain,(
    ! [A_6876] :
      ( k9_relat_1(A_6876,k1_relat_1('#skF_6')) = k11_relat_1(A_6876,'#skF_3')
      | ~ v1_relat_1(A_6876) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_303,c_44])).

tff(c_4639,plain,
    ( k11_relat_1('#skF_6','#skF_3') = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_4629,c_403])).

tff(c_4662,plain,(
    k11_relat_1('#skF_6','#skF_3') = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_4639])).

tff(c_84,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_94,plain,(
    ! [D_44,B_45] : r2_hidden(D_44,k2_tarski(D_44,B_45)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_97,plain,(
    ! [A_7] : r2_hidden(A_7,k1_tarski(A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_94])).

tff(c_340,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_303,c_97])).

tff(c_56,plain,(
    ! [B_29,A_28] :
      ( k1_tarski(k1_funct_1(B_29,A_28)) = k11_relat_1(B_29,A_28)
      | ~ r2_hidden(A_28,k1_relat_1(B_29))
      | ~ v1_funct_1(B_29)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_348,plain,
    ( k1_tarski(k1_funct_1('#skF_6','#skF_3')) = k11_relat_1('#skF_6','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_340,c_56])).

tff(c_351,plain,(
    k1_tarski(k1_funct_1('#skF_6','#skF_3')) = k11_relat_1('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_84,c_348])).

tff(c_268,plain,(
    ! [A_116,B_117,C_118,D_119] :
      ( k7_relset_1(A_116,B_117,C_118,D_119) = k9_relat_1(C_118,D_119)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_271,plain,(
    ! [D_119] : k7_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6',D_119) = k9_relat_1('#skF_6',D_119) ),
    inference(resolution,[status(thm)],[c_80,c_268])).

tff(c_76,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6','#skF_5'),k1_tarski(k1_funct_1('#skF_6','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_272,plain,(
    ~ r1_tarski(k9_relat_1('#skF_6','#skF_5'),k1_tarski(k1_funct_1('#skF_6','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_76])).

tff(c_3718,plain,(
    ~ r1_tarski(k9_relat_1('#skF_6','#skF_5'),k11_relat_1('#skF_6','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_351,c_272])).

tff(c_4668,plain,(
    ~ r1_tarski(k9_relat_1('#skF_6','#skF_5'),k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4662,c_3718])).

tff(c_4674,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1992,c_4668])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:52:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.53/1.81  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.60/1.81  
% 4.60/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.62/1.82  %$ v1_funct_2 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 4.62/1.82  
% 4.62/1.82  %Foreground sorts:
% 4.62/1.82  
% 4.62/1.82  
% 4.62/1.82  %Background operators:
% 4.62/1.82  
% 4.62/1.82  
% 4.62/1.82  %Foreground operators:
% 4.62/1.82  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.62/1.82  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.62/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.62/1.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.62/1.82  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.62/1.82  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.62/1.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.62/1.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.62/1.82  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.62/1.82  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.62/1.82  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.62/1.82  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.62/1.82  tff('#skF_5', type, '#skF_5': $i).
% 4.62/1.82  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.62/1.82  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 4.62/1.82  tff('#skF_6', type, '#skF_6': $i).
% 4.62/1.82  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.62/1.82  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.62/1.82  tff('#skF_3', type, '#skF_3': $i).
% 4.62/1.82  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.62/1.82  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.62/1.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.62/1.82  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.62/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.62/1.82  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.62/1.82  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.62/1.82  tff('#skF_4', type, '#skF_4': $i).
% 4.62/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.62/1.82  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.62/1.82  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.62/1.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.62/1.82  
% 4.62/1.83  tff(f_142, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 4.62/1.83  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.62/1.83  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.62/1.83  tff(f_130, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.62/1.83  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.62/1.83  tff(f_38, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 4.62/1.83  tff(f_67, axiom, (![A, B, C, D]: (r1_tarski(D, k1_enumset1(A, B, C)) <=> ~(((((((~(D = k1_xboole_0) & ~(D = k1_tarski(A))) & ~(D = k1_tarski(B))) & ~(D = k1_tarski(C))) & ~(D = k2_tarski(A, B))) & ~(D = k2_tarski(B, C))) & ~(D = k2_tarski(A, C))) & ~(D = k1_enumset1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 4.62/1.83  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 4.62/1.83  tff(f_92, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 4.62/1.83  tff(f_86, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 4.62/1.83  tff(f_82, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 4.62/1.83  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 4.62/1.83  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 4.62/1.83  tff(f_100, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k11_relat_1(B, A) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_funct_1)).
% 4.62/1.83  tff(f_112, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.62/1.83  tff(c_80, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.62/1.83  tff(c_131, plain, (![C_65, A_66, B_67]: (v1_relat_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.62/1.83  tff(c_135, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_80, c_131])).
% 4.62/1.83  tff(c_78, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.62/1.83  tff(c_82, plain, (v1_funct_2('#skF_6', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.62/1.83  tff(c_257, plain, (![A_110, B_111, C_112]: (k1_relset_1(A_110, B_111, C_112)=k1_relat_1(C_112) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.62/1.83  tff(c_261, plain, (k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_80, c_257])).
% 4.62/1.83  tff(c_296, plain, (![B_139, A_140, C_141]: (k1_xboole_0=B_139 | k1_relset_1(A_140, B_139, C_141)=A_140 | ~v1_funct_2(C_141, A_140, B_139) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_140, B_139))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.62/1.83  tff(c_299, plain, (k1_xboole_0='#skF_4' | k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6')=k1_tarski('#skF_3') | ~v1_funct_2('#skF_6', k1_tarski('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_80, c_296])).
% 4.62/1.83  tff(c_302, plain, (k1_xboole_0='#skF_4' | k1_tarski('#skF_3')=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_261, c_299])).
% 4.62/1.83  tff(c_303, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_78, c_302])).
% 4.62/1.83  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.62/1.83  tff(c_108, plain, (![A_61, B_62]: (k1_enumset1(A_61, A_61, B_62)=k2_tarski(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.62/1.83  tff(c_36, plain, (![C_15, A_13, B_14]: (r1_tarski(k1_tarski(C_15), k1_enumset1(A_13, B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.62/1.83  tff(c_137, plain, (![B_69, A_70]: (r1_tarski(k1_tarski(B_69), k2_tarski(A_70, B_69)))), inference(superposition, [status(thm), theory('equality')], [c_108, c_36])).
% 4.62/1.83  tff(c_140, plain, (![A_7]: (r1_tarski(k1_tarski(A_7), k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_137])).
% 4.62/1.83  tff(c_323, plain, (r1_tarski(k1_tarski('#skF_3'), k1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_303, c_140])).
% 4.62/1.83  tff(c_344, plain, (r1_tarski(k1_relat_1('#skF_6'), k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_303, c_323])).
% 4.62/1.83  tff(c_46, plain, (![B_21, A_20]: (v4_relat_1(B_21, A_20) | ~r1_tarski(k1_relat_1(B_21), A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.62/1.83  tff(c_355, plain, (v4_relat_1('#skF_6', k1_relat_1('#skF_6')) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_344, c_46])).
% 4.62/1.83  tff(c_358, plain, (v4_relat_1('#skF_6', k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_355])).
% 4.62/1.83  tff(c_54, plain, (![B_27, A_26]: (k7_relat_1(B_27, A_26)=B_27 | ~v4_relat_1(B_27, A_26) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.62/1.83  tff(c_386, plain, (k7_relat_1('#skF_6', k1_relat_1('#skF_6'))='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_358, c_54])).
% 4.62/1.83  tff(c_389, plain, (k7_relat_1('#skF_6', k1_relat_1('#skF_6'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_135, c_386])).
% 4.62/1.83  tff(c_52, plain, (![B_25, A_24]: (k2_relat_1(k7_relat_1(B_25, A_24))=k9_relat_1(B_25, A_24) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.62/1.83  tff(c_397, plain, (k9_relat_1('#skF_6', k1_relat_1('#skF_6'))=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_389, c_52])).
% 4.62/1.83  tff(c_403, plain, (k9_relat_1('#skF_6', k1_relat_1('#skF_6'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_135, c_397])).
% 4.62/1.83  tff(c_236, plain, (![B_104, A_105]: (k2_relat_1(k7_relat_1(B_104, A_105))=k9_relat_1(B_104, A_105) | ~v1_relat_1(B_104))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.62/1.83  tff(c_50, plain, (![B_23, A_22]: (r1_tarski(k9_relat_1(B_23, A_22), k2_relat_1(B_23)) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.62/1.83  tff(c_242, plain, (![B_104, A_105, A_22]: (r1_tarski(k9_relat_1(k7_relat_1(B_104, A_105), A_22), k9_relat_1(B_104, A_105)) | ~v1_relat_1(k7_relat_1(B_104, A_105)) | ~v1_relat_1(B_104))), inference(superposition, [status(thm), theory('equality')], [c_236, c_50])).
% 4.62/1.83  tff(c_1984, plain, (![A_22]: (r1_tarski(k9_relat_1(k7_relat_1('#skF_6', k1_relat_1('#skF_6')), A_22), k2_relat_1('#skF_6')) | ~v1_relat_1(k7_relat_1('#skF_6', k1_relat_1('#skF_6'))) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_403, c_242])).
% 4.62/1.83  tff(c_1992, plain, (![A_22]: (r1_tarski(k9_relat_1('#skF_6', A_22), k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_135, c_389, c_389, c_1984])).
% 4.62/1.83  tff(c_44, plain, (![A_17, B_19]: (k9_relat_1(A_17, k1_tarski(B_19))=k11_relat_1(A_17, B_19) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.62/1.83  tff(c_4629, plain, (![A_6876]: (k9_relat_1(A_6876, k1_relat_1('#skF_6'))=k11_relat_1(A_6876, '#skF_3') | ~v1_relat_1(A_6876))), inference(superposition, [status(thm), theory('equality')], [c_303, c_44])).
% 4.62/1.83  tff(c_4639, plain, (k11_relat_1('#skF_6', '#skF_3')=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_4629, c_403])).
% 4.62/1.83  tff(c_4662, plain, (k11_relat_1('#skF_6', '#skF_3')=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_135, c_4639])).
% 4.62/1.83  tff(c_84, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.62/1.83  tff(c_94, plain, (![D_44, B_45]: (r2_hidden(D_44, k2_tarski(D_44, B_45)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.62/1.83  tff(c_97, plain, (![A_7]: (r2_hidden(A_7, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_94])).
% 4.62/1.83  tff(c_340, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_303, c_97])).
% 4.62/1.83  tff(c_56, plain, (![B_29, A_28]: (k1_tarski(k1_funct_1(B_29, A_28))=k11_relat_1(B_29, A_28) | ~r2_hidden(A_28, k1_relat_1(B_29)) | ~v1_funct_1(B_29) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.62/1.83  tff(c_348, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_3'))=k11_relat_1('#skF_6', '#skF_3') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_340, c_56])).
% 4.62/1.83  tff(c_351, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_3'))=k11_relat_1('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_135, c_84, c_348])).
% 4.62/1.83  tff(c_268, plain, (![A_116, B_117, C_118, D_119]: (k7_relset_1(A_116, B_117, C_118, D_119)=k9_relat_1(C_118, D_119) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.62/1.83  tff(c_271, plain, (![D_119]: (k7_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6', D_119)=k9_relat_1('#skF_6', D_119))), inference(resolution, [status(thm)], [c_80, c_268])).
% 4.62/1.83  tff(c_76, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6', '#skF_5'), k1_tarski(k1_funct_1('#skF_6', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.62/1.83  tff(c_272, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_5'), k1_tarski(k1_funct_1('#skF_6', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_271, c_76])).
% 4.62/1.83  tff(c_3718, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_5'), k11_relat_1('#skF_6', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_351, c_272])).
% 4.62/1.83  tff(c_4668, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_5'), k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_4662, c_3718])).
% 4.62/1.83  tff(c_4674, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1992, c_4668])).
% 4.62/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.62/1.83  
% 4.62/1.83  Inference rules
% 4.62/1.83  ----------------------
% 4.62/1.83  #Ref     : 0
% 4.62/1.83  #Sup     : 472
% 4.62/1.83  #Fact    : 4
% 4.62/1.83  #Define  : 0
% 4.62/1.83  #Split   : 0
% 4.62/1.83  #Chain   : 0
% 4.62/1.83  #Close   : 0
% 4.62/1.83  
% 4.62/1.83  Ordering : KBO
% 4.62/1.83  
% 4.62/1.83  Simplification rules
% 4.62/1.83  ----------------------
% 4.62/1.83  #Subsume      : 13
% 4.62/1.83  #Demod        : 180
% 4.62/1.83  #Tautology    : 157
% 4.62/1.83  #SimpNegUnit  : 3
% 4.62/1.83  #BackRed      : 11
% 4.62/1.83  
% 4.62/1.83  #Partial instantiations: 3906
% 4.62/1.83  #Strategies tried      : 1
% 4.62/1.83  
% 4.62/1.83  Timing (in seconds)
% 4.62/1.83  ----------------------
% 4.62/1.83  Preprocessing        : 0.35
% 4.62/1.83  Parsing              : 0.18
% 4.62/1.83  CNF conversion       : 0.02
% 4.62/1.83  Main loop            : 0.71
% 4.62/1.83  Inferencing          : 0.38
% 4.62/1.83  Reduction            : 0.18
% 4.62/1.83  Demodulation         : 0.14
% 4.62/1.83  BG Simplification    : 0.04
% 4.62/1.83  Subsumption          : 0.08
% 4.62/1.83  Abstraction          : 0.03
% 4.62/1.84  MUC search           : 0.00
% 4.62/1.84  Cooper               : 0.00
% 4.62/1.84  Total                : 1.09
% 4.62/1.84  Index Insertion      : 0.00
% 4.62/1.84  Index Deletion       : 0.00
% 4.62/1.84  Index Matching       : 0.00
% 4.62/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
