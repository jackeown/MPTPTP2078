%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:44 EST 2020

% Result     : Theorem 3.19s
% Output     : CNFRefutation 3.30s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 428 expanded)
%              Number of leaves         :   44 ( 160 expanded)
%              Depth                    :   12
%              Number of atoms          :  155 ( 912 expanded)
%              Number of equality atoms :   54 ( 274 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(f_122,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_86,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k1_relat_1(C)) )
       => k9_relat_1(C,k2_tarski(A,B)) = k2_tarski(k1_funct_1(C,A),k1_funct_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_funct_1)).

tff(f_110,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_78,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_49,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_143,plain,(
    ! [C_54,A_55,B_56] :
      ( v1_relat_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_151,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_143])).

tff(c_44,plain,(
    ! [A_23] :
      ( k1_relat_1(A_23) != k1_xboole_0
      | k1_xboole_0 = A_23
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_159,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_151,c_44])).

tff(c_175,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_159])).

tff(c_271,plain,(
    ! [C_74,A_75,B_76] :
      ( v4_relat_1(C_74,A_75)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_279,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_60,c_271])).

tff(c_328,plain,(
    ! [B_79,A_80] :
      ( r1_tarski(k1_relat_1(B_79),A_80)
      | ~ v4_relat_1(B_79,A_80)
      | ~ v1_relat_1(B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_18,plain,(
    ! [B_10,A_9] :
      ( k1_tarski(B_10) = A_9
      | k1_xboole_0 = A_9
      | ~ r1_tarski(A_9,k1_tarski(B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_538,plain,(
    ! [B_109,B_110] :
      ( k1_tarski(B_109) = k1_relat_1(B_110)
      | k1_relat_1(B_110) = k1_xboole_0
      | ~ v4_relat_1(B_110,k1_tarski(B_109))
      | ~ v1_relat_1(B_110) ) ),
    inference(resolution,[status(thm)],[c_328,c_18])).

tff(c_541,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_279,c_538])).

tff(c_548,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_541])).

tff(c_549,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_175,c_548])).

tff(c_36,plain,(
    ! [B_22,A_21] :
      ( k7_relat_1(B_22,A_21) = B_22
      | ~ v4_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_284,plain,
    ( k7_relat_1('#skF_4',k1_tarski('#skF_1')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_279,c_36])).

tff(c_287,plain,(
    k7_relat_1('#skF_4',k1_tarski('#skF_1')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_284])).

tff(c_556,plain,(
    k7_relat_1('#skF_4',k1_relat_1('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_549,c_287])).

tff(c_34,plain,(
    ! [B_20,A_19] :
      ( k2_relat_1(k7_relat_1(B_20,A_19)) = k9_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_303,plain,
    ( k9_relat_1('#skF_4',k1_tarski('#skF_1')) = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_34])).

tff(c_307,plain,(
    k9_relat_1('#skF_4',k1_tarski('#skF_1')) = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_303])).

tff(c_555,plain,(
    k9_relat_1('#skF_4',k1_relat_1('#skF_4')) = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_549,c_307])).

tff(c_230,plain,(
    ! [B_65,A_66] :
      ( k2_relat_1(k7_relat_1(B_65,A_66)) = k9_relat_1(B_65,A_66)
      | ~ v1_relat_1(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_32,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k9_relat_1(B_18,A_17),k2_relat_1(B_18))
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_744,plain,(
    ! [B_115,A_116,A_117] :
      ( r1_tarski(k9_relat_1(k7_relat_1(B_115,A_116),A_117),k9_relat_1(B_115,A_116))
      | ~ v1_relat_1(k7_relat_1(B_115,A_116))
      | ~ v1_relat_1(B_115) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_32])).

tff(c_752,plain,(
    ! [A_117] :
      ( r1_tarski(k9_relat_1('#skF_4',A_117),k9_relat_1('#skF_4',k1_relat_1('#skF_4')))
      | ~ v1_relat_1(k7_relat_1('#skF_4',k1_relat_1('#skF_4')))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_556,c_744])).

tff(c_773,plain,(
    ! [A_117] : r1_tarski(k9_relat_1('#skF_4',A_117),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_151,c_556,c_555,c_752])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_90,plain,(
    ! [A_44,B_45] :
      ( r2_hidden(A_44,B_45)
      | ~ r1_tarski(k1_tarski(A_44),B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_99,plain,(
    ! [A_44] : r2_hidden(A_44,k1_tarski(A_44)) ),
    inference(resolution,[status(thm)],[c_6,c_90])).

tff(c_577,plain,(
    r2_hidden('#skF_1',k1_relat_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_549,c_99])).

tff(c_10,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_512,plain,(
    ! [C_104,A_105,B_106] :
      ( k2_tarski(k1_funct_1(C_104,A_105),k1_funct_1(C_104,B_106)) = k9_relat_1(C_104,k2_tarski(A_105,B_106))
      | ~ r2_hidden(B_106,k1_relat_1(C_104))
      | ~ r2_hidden(A_105,k1_relat_1(C_104))
      | ~ v1_funct_1(C_104)
      | ~ v1_relat_1(C_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_519,plain,(
    ! [C_104,B_106] :
      ( k9_relat_1(C_104,k2_tarski(B_106,B_106)) = k1_tarski(k1_funct_1(C_104,B_106))
      | ~ r2_hidden(B_106,k1_relat_1(C_104))
      | ~ r2_hidden(B_106,k1_relat_1(C_104))
      | ~ v1_funct_1(C_104)
      | ~ v1_relat_1(C_104) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_512,c_10])).

tff(c_920,plain,(
    ! [C_125,B_126] :
      ( k9_relat_1(C_125,k1_tarski(B_126)) = k1_tarski(k1_funct_1(C_125,B_126))
      | ~ r2_hidden(B_126,k1_relat_1(C_125))
      | ~ r2_hidden(B_126,k1_relat_1(C_125))
      | ~ v1_funct_1(C_125)
      | ~ v1_relat_1(C_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_519])).

tff(c_922,plain,
    ( k9_relat_1('#skF_4',k1_tarski('#skF_1')) = k1_tarski(k1_funct_1('#skF_4','#skF_1'))
    | ~ r2_hidden('#skF_1',k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_577,c_920])).

tff(c_927,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_1')) = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_64,c_577,c_555,c_549,c_922])).

tff(c_486,plain,(
    ! [A_96,B_97,C_98,D_99] :
      ( k7_relset_1(A_96,B_97,C_98,D_99) = k9_relat_1(C_98,D_99)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_492,plain,(
    ! [D_99] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_99) = k9_relat_1('#skF_4',D_99) ),
    inference(resolution,[status(thm)],[c_60,c_486])).

tff(c_56,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_502,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_492,c_56])).

tff(c_930,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_927,c_502])).

tff(c_933,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_773,c_930])).

tff(c_934,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_159])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_943,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_934,c_8])).

tff(c_38,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_942,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_934,c_934,c_38])).

tff(c_974,plain,(
    ! [B_129,A_130] :
      ( r1_tarski(k9_relat_1(B_129,A_130),k2_relat_1(B_129))
      | ~ v1_relat_1(B_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_979,plain,(
    ! [A_130] :
      ( r1_tarski(k9_relat_1('#skF_4',A_130),'#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_942,c_974])).

tff(c_1001,plain,(
    ! [A_132] : r1_tarski(k9_relat_1('#skF_4',A_132),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_979])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1006,plain,(
    ! [A_132] :
      ( k9_relat_1('#skF_4',A_132) = '#skF_4'
      | ~ r1_tarski('#skF_4',k9_relat_1('#skF_4',A_132)) ) ),
    inference(resolution,[status(thm)],[c_1001,c_2])).

tff(c_1010,plain,(
    ! [A_132] : k9_relat_1('#skF_4',A_132) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_943,c_1006])).

tff(c_24,plain,(
    ! [A_11] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_941,plain,(
    ! [A_11] : m1_subset_1('#skF_4',k1_zfmisc_1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_934,c_24])).

tff(c_1195,plain,(
    ! [A_162,B_163,C_164,D_165] :
      ( k7_relset_1(A_162,B_163,C_164,D_165) = k9_relat_1(C_164,D_165)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(A_162,B_163))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1198,plain,(
    ! [A_162,B_163,D_165] : k7_relset_1(A_162,B_163,'#skF_4',D_165) = k9_relat_1('#skF_4',D_165) ),
    inference(resolution,[status(thm)],[c_941,c_1195])).

tff(c_1200,plain,(
    ! [A_162,B_163,D_165] : k7_relset_1(A_162,B_163,'#skF_4',D_165) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1010,c_1198])).

tff(c_1202,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1200,c_56])).

tff(c_1205,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_943,c_1202])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:24:11 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.19/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.30/1.50  
% 3.30/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.30/1.50  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.30/1.50  
% 3.30/1.50  %Foreground sorts:
% 3.30/1.50  
% 3.30/1.50  
% 3.30/1.50  %Background operators:
% 3.30/1.50  
% 3.30/1.50  
% 3.30/1.50  %Foreground operators:
% 3.30/1.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.30/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.30/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.30/1.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.30/1.50  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.30/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.30/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.30/1.50  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.30/1.50  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.30/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.30/1.50  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.30/1.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.30/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.30/1.50  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.30/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.30/1.50  tff('#skF_1', type, '#skF_1': $i).
% 3.30/1.50  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.30/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.30/1.50  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.30/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.30/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.30/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.30/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.30/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.30/1.50  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.30/1.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.30/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.30/1.50  
% 3.30/1.52  tff(f_122, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 3.30/1.52  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.30/1.52  tff(f_86, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 3.30/1.52  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.30/1.52  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.30/1.52  tff(f_47, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.30/1.52  tff(f_75, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.30/1.52  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.30/1.52  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 3.30/1.52  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.30/1.52  tff(f_41, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.30/1.52  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.30/1.52  tff(f_96, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k1_relat_1(C))) => (k9_relat_1(C, k2_tarski(A, B)) = k2_tarski(k1_funct_1(C, A), k1_funct_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_funct_1)).
% 3.30/1.52  tff(f_110, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.30/1.52  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.30/1.52  tff(f_78, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.30/1.52  tff(f_49, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.30/1.52  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.30/1.52  tff(c_143, plain, (![C_54, A_55, B_56]: (v1_relat_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.30/1.52  tff(c_151, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_143])).
% 3.30/1.52  tff(c_44, plain, (![A_23]: (k1_relat_1(A_23)!=k1_xboole_0 | k1_xboole_0=A_23 | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.30/1.52  tff(c_159, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_151, c_44])).
% 3.30/1.52  tff(c_175, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_159])).
% 3.30/1.52  tff(c_271, plain, (![C_74, A_75, B_76]: (v4_relat_1(C_74, A_75) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.30/1.52  tff(c_279, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_60, c_271])).
% 3.30/1.52  tff(c_328, plain, (![B_79, A_80]: (r1_tarski(k1_relat_1(B_79), A_80) | ~v4_relat_1(B_79, A_80) | ~v1_relat_1(B_79))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.30/1.52  tff(c_18, plain, (![B_10, A_9]: (k1_tarski(B_10)=A_9 | k1_xboole_0=A_9 | ~r1_tarski(A_9, k1_tarski(B_10)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.30/1.52  tff(c_538, plain, (![B_109, B_110]: (k1_tarski(B_109)=k1_relat_1(B_110) | k1_relat_1(B_110)=k1_xboole_0 | ~v4_relat_1(B_110, k1_tarski(B_109)) | ~v1_relat_1(B_110))), inference(resolution, [status(thm)], [c_328, c_18])).
% 3.30/1.52  tff(c_541, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_279, c_538])).
% 3.30/1.52  tff(c_548, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_151, c_541])).
% 3.30/1.52  tff(c_549, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_175, c_548])).
% 3.30/1.52  tff(c_36, plain, (![B_22, A_21]: (k7_relat_1(B_22, A_21)=B_22 | ~v4_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.30/1.52  tff(c_284, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_1'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_279, c_36])).
% 3.30/1.52  tff(c_287, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_1'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_151, c_284])).
% 3.30/1.52  tff(c_556, plain, (k7_relat_1('#skF_4', k1_relat_1('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_549, c_287])).
% 3.30/1.52  tff(c_34, plain, (![B_20, A_19]: (k2_relat_1(k7_relat_1(B_20, A_19))=k9_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.30/1.52  tff(c_303, plain, (k9_relat_1('#skF_4', k1_tarski('#skF_1'))=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_287, c_34])).
% 3.30/1.52  tff(c_307, plain, (k9_relat_1('#skF_4', k1_tarski('#skF_1'))=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_151, c_303])).
% 3.30/1.52  tff(c_555, plain, (k9_relat_1('#skF_4', k1_relat_1('#skF_4'))=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_549, c_307])).
% 3.30/1.52  tff(c_230, plain, (![B_65, A_66]: (k2_relat_1(k7_relat_1(B_65, A_66))=k9_relat_1(B_65, A_66) | ~v1_relat_1(B_65))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.30/1.52  tff(c_32, plain, (![B_18, A_17]: (r1_tarski(k9_relat_1(B_18, A_17), k2_relat_1(B_18)) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.30/1.52  tff(c_744, plain, (![B_115, A_116, A_117]: (r1_tarski(k9_relat_1(k7_relat_1(B_115, A_116), A_117), k9_relat_1(B_115, A_116)) | ~v1_relat_1(k7_relat_1(B_115, A_116)) | ~v1_relat_1(B_115))), inference(superposition, [status(thm), theory('equality')], [c_230, c_32])).
% 3.30/1.52  tff(c_752, plain, (![A_117]: (r1_tarski(k9_relat_1('#skF_4', A_117), k9_relat_1('#skF_4', k1_relat_1('#skF_4'))) | ~v1_relat_1(k7_relat_1('#skF_4', k1_relat_1('#skF_4'))) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_556, c_744])).
% 3.30/1.52  tff(c_773, plain, (![A_117]: (r1_tarski(k9_relat_1('#skF_4', A_117), k2_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_151, c_151, c_556, c_555, c_752])).
% 3.30/1.52  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.30/1.52  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.30/1.52  tff(c_90, plain, (![A_44, B_45]: (r2_hidden(A_44, B_45) | ~r1_tarski(k1_tarski(A_44), B_45))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.30/1.52  tff(c_99, plain, (![A_44]: (r2_hidden(A_44, k1_tarski(A_44)))), inference(resolution, [status(thm)], [c_6, c_90])).
% 3.30/1.52  tff(c_577, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_549, c_99])).
% 3.30/1.52  tff(c_10, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.30/1.52  tff(c_512, plain, (![C_104, A_105, B_106]: (k2_tarski(k1_funct_1(C_104, A_105), k1_funct_1(C_104, B_106))=k9_relat_1(C_104, k2_tarski(A_105, B_106)) | ~r2_hidden(B_106, k1_relat_1(C_104)) | ~r2_hidden(A_105, k1_relat_1(C_104)) | ~v1_funct_1(C_104) | ~v1_relat_1(C_104))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.30/1.52  tff(c_519, plain, (![C_104, B_106]: (k9_relat_1(C_104, k2_tarski(B_106, B_106))=k1_tarski(k1_funct_1(C_104, B_106)) | ~r2_hidden(B_106, k1_relat_1(C_104)) | ~r2_hidden(B_106, k1_relat_1(C_104)) | ~v1_funct_1(C_104) | ~v1_relat_1(C_104))), inference(superposition, [status(thm), theory('equality')], [c_512, c_10])).
% 3.30/1.52  tff(c_920, plain, (![C_125, B_126]: (k9_relat_1(C_125, k1_tarski(B_126))=k1_tarski(k1_funct_1(C_125, B_126)) | ~r2_hidden(B_126, k1_relat_1(C_125)) | ~r2_hidden(B_126, k1_relat_1(C_125)) | ~v1_funct_1(C_125) | ~v1_relat_1(C_125))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_519])).
% 3.30/1.52  tff(c_922, plain, (k9_relat_1('#skF_4', k1_tarski('#skF_1'))=k1_tarski(k1_funct_1('#skF_4', '#skF_1')) | ~r2_hidden('#skF_1', k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_577, c_920])).
% 3.30/1.52  tff(c_927, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_1'))=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_151, c_64, c_577, c_555, c_549, c_922])).
% 3.30/1.52  tff(c_486, plain, (![A_96, B_97, C_98, D_99]: (k7_relset_1(A_96, B_97, C_98, D_99)=k9_relat_1(C_98, D_99) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.30/1.52  tff(c_492, plain, (![D_99]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_99)=k9_relat_1('#skF_4', D_99))), inference(resolution, [status(thm)], [c_60, c_486])).
% 3.30/1.52  tff(c_56, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.30/1.52  tff(c_502, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_492, c_56])).
% 3.30/1.52  tff(c_930, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_927, c_502])).
% 3.30/1.52  tff(c_933, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_773, c_930])).
% 3.30/1.52  tff(c_934, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_159])).
% 3.30/1.52  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.30/1.52  tff(c_943, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_934, c_8])).
% 3.30/1.52  tff(c_38, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.30/1.52  tff(c_942, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_934, c_934, c_38])).
% 3.30/1.52  tff(c_974, plain, (![B_129, A_130]: (r1_tarski(k9_relat_1(B_129, A_130), k2_relat_1(B_129)) | ~v1_relat_1(B_129))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.30/1.52  tff(c_979, plain, (![A_130]: (r1_tarski(k9_relat_1('#skF_4', A_130), '#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_942, c_974])).
% 3.30/1.52  tff(c_1001, plain, (![A_132]: (r1_tarski(k9_relat_1('#skF_4', A_132), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_151, c_979])).
% 3.30/1.52  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.30/1.52  tff(c_1006, plain, (![A_132]: (k9_relat_1('#skF_4', A_132)='#skF_4' | ~r1_tarski('#skF_4', k9_relat_1('#skF_4', A_132)))), inference(resolution, [status(thm)], [c_1001, c_2])).
% 3.30/1.52  tff(c_1010, plain, (![A_132]: (k9_relat_1('#skF_4', A_132)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_943, c_1006])).
% 3.30/1.52  tff(c_24, plain, (![A_11]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.30/1.52  tff(c_941, plain, (![A_11]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_934, c_24])).
% 3.30/1.52  tff(c_1195, plain, (![A_162, B_163, C_164, D_165]: (k7_relset_1(A_162, B_163, C_164, D_165)=k9_relat_1(C_164, D_165) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(A_162, B_163))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.30/1.52  tff(c_1198, plain, (![A_162, B_163, D_165]: (k7_relset_1(A_162, B_163, '#skF_4', D_165)=k9_relat_1('#skF_4', D_165))), inference(resolution, [status(thm)], [c_941, c_1195])).
% 3.30/1.52  tff(c_1200, plain, (![A_162, B_163, D_165]: (k7_relset_1(A_162, B_163, '#skF_4', D_165)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1010, c_1198])).
% 3.30/1.52  tff(c_1202, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1200, c_56])).
% 3.30/1.52  tff(c_1205, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_943, c_1202])).
% 3.30/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.30/1.52  
% 3.30/1.52  Inference rules
% 3.30/1.52  ----------------------
% 3.30/1.52  #Ref     : 0
% 3.30/1.52  #Sup     : 224
% 3.30/1.52  #Fact    : 0
% 3.30/1.52  #Define  : 0
% 3.30/1.52  #Split   : 2
% 3.30/1.52  #Chain   : 0
% 3.30/1.52  #Close   : 0
% 3.30/1.52  
% 3.30/1.52  Ordering : KBO
% 3.30/1.52  
% 3.30/1.52  Simplification rules
% 3.30/1.52  ----------------------
% 3.30/1.52  #Subsume      : 9
% 3.30/1.52  #Demod        : 215
% 3.30/1.52  #Tautology    : 142
% 3.30/1.52  #SimpNegUnit  : 5
% 3.30/1.52  #BackRed      : 22
% 3.30/1.52  
% 3.30/1.52  #Partial instantiations: 0
% 3.30/1.52  #Strategies tried      : 1
% 3.30/1.52  
% 3.30/1.52  Timing (in seconds)
% 3.30/1.52  ----------------------
% 3.42/1.53  Preprocessing        : 0.34
% 3.42/1.53  Parsing              : 0.18
% 3.42/1.53  CNF conversion       : 0.02
% 3.42/1.53  Main loop            : 0.41
% 3.42/1.53  Inferencing          : 0.15
% 3.42/1.53  Reduction            : 0.13
% 3.42/1.53  Demodulation         : 0.09
% 3.42/1.53  BG Simplification    : 0.02
% 3.42/1.53  Subsumption          : 0.07
% 3.42/1.53  Abstraction          : 0.02
% 3.42/1.53  MUC search           : 0.00
% 3.42/1.53  Cooper               : 0.00
% 3.42/1.53  Total                : 0.78
% 3.42/1.53  Index Insertion      : 0.00
% 3.42/1.53  Index Deletion       : 0.00
% 3.42/1.53  Index Matching       : 0.00
% 3.42/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
