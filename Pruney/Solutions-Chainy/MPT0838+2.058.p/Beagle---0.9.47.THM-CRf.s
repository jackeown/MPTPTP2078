%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:17 EST 2020

% Result     : Theorem 3.47s
% Output     : CNFRefutation 3.61s
% Verified   : 
% Statistics : Number of formulae       :  183 ( 933 expanded)
%              Number of leaves         :   39 ( 325 expanded)
%              Depth                    :   16
%              Number of atoms          :  307 (2105 expanded)
%              Number of equality atoms :   30 ( 256 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v3_relat_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v3_relat_1,type,(
    v3_relat_1: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_120,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
               => ~ ( k1_relset_1(A,B,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k2_relset_1(A,B,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relset_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_68,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_39,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v3_relat_1(A)
      <=> ! [B] :
            ( r2_hidden(B,k2_relat_1(A))
           => B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t184_relat_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_76,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

tff(c_46,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1637,plain,(
    ! [A_280,B_281,C_282] :
      ( k1_relset_1(A_280,B_281,C_282) = k1_relat_1(C_282)
      | ~ m1_subset_1(C_282,k1_zfmisc_1(k2_zfmisc_1(A_280,B_281))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1655,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_1637])).

tff(c_44,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1657,plain,(
    k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1655,c_44])).

tff(c_24,plain,(
    ! [A_19,B_20] : v1_relat_1(k2_zfmisc_1(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1045,plain,(
    ! [B_183,A_184] :
      ( v1_relat_1(B_183)
      | ~ m1_subset_1(B_183,k1_zfmisc_1(A_184))
      | ~ v1_relat_1(A_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1048,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_46,c_1045])).

tff(c_1055,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1048])).

tff(c_137,plain,(
    ! [B_69,A_70] :
      ( v1_relat_1(B_69)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_70))
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_140,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_46,c_137])).

tff(c_147,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_140])).

tff(c_10,plain,(
    ! [A_7] : m1_subset_1('#skF_2'(A_7),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    ! [A_18] :
      ( v1_xboole_0(k1_relat_1(A_18))
      | ~ v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_54,plain,(
    ! [A_51] :
      ( v1_xboole_0(k1_relat_1(A_51))
      | ~ v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_8,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_59,plain,(
    ! [A_52] :
      ( k1_relat_1(A_52) = k1_xboole_0
      | ~ v1_xboole_0(A_52) ) ),
    inference(resolution,[status(thm)],[c_54,c_8])).

tff(c_66,plain,(
    ! [A_56] :
      ( k1_relat_1(k1_relat_1(A_56)) = k1_xboole_0
      | ~ v1_xboole_0(A_56) ) ),
    inference(resolution,[status(thm)],[c_22,c_59])).

tff(c_75,plain,(
    ! [A_56] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(k1_relat_1(A_56))
      | ~ v1_xboole_0(A_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_22])).

tff(c_97,plain,(
    ! [A_61] :
      ( ~ v1_xboole_0(k1_relat_1(A_61))
      | ~ v1_xboole_0(A_61) ) ),
    inference(splitLeft,[status(thm)],[c_75])).

tff(c_104,plain,(
    ! [A_18] : ~ v1_xboole_0(A_18) ),
    inference(resolution,[status(thm)],[c_22,c_97])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( r2_hidden(A_11,B_12)
      | v1_xboole_0(B_12)
      | ~ m1_subset_1(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_108,plain,(
    ! [A_11,B_12] :
      ( r2_hidden(A_11,B_12)
      | ~ m1_subset_1(A_11,B_12) ) ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_14])).

tff(c_236,plain,(
    ! [B_100,A_101] :
      ( k1_xboole_0 = B_100
      | ~ r2_hidden(B_100,k2_relat_1(A_101))
      | ~ v3_relat_1(A_101)
      | ~ v1_relat_1(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_271,plain,(
    ! [A_105,A_106] :
      ( k1_xboole_0 = A_105
      | ~ v3_relat_1(A_106)
      | ~ v1_relat_1(A_106)
      | ~ m1_subset_1(A_105,k2_relat_1(A_106)) ) ),
    inference(resolution,[status(thm)],[c_108,c_236])).

tff(c_346,plain,(
    ! [A_112] :
      ( '#skF_2'(k2_relat_1(A_112)) = k1_xboole_0
      | ~ v3_relat_1(A_112)
      | ~ v1_relat_1(A_112) ) ),
    inference(resolution,[status(thm)],[c_10,c_271])).

tff(c_286,plain,(
    ! [A_107,B_108,C_109] :
      ( k2_relset_1(A_107,B_108,C_109) = k2_relat_1(C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_299,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_286])).

tff(c_109,plain,(
    ! [A_63,B_64] :
      ( r2_hidden(A_63,B_64)
      | ~ m1_subset_1(A_63,B_64) ) ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_14])).

tff(c_42,plain,(
    ! [D_46] :
      ( ~ r2_hidden(D_46,k2_relset_1('#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1(D_46,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_119,plain,(
    ! [A_65] :
      ( ~ m1_subset_1(A_65,'#skF_5')
      | ~ m1_subset_1(A_65,k2_relset_1('#skF_4','#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_109,c_42])).

tff(c_124,plain,(
    ~ m1_subset_1('#skF_2'(k2_relset_1('#skF_4','#skF_5','#skF_6')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_119])).

tff(c_302,plain,(
    ~ m1_subset_1('#skF_2'(k2_relat_1('#skF_6')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_124])).

tff(c_352,plain,
    ( ~ m1_subset_1(k1_xboole_0,'#skF_5')
    | ~ v3_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_346,c_302])).

tff(c_361,plain,
    ( ~ m1_subset_1(k1_xboole_0,'#skF_5')
    | ~ v3_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_352])).

tff(c_363,plain,(
    ~ v3_relat_1('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_361])).

tff(c_202,plain,(
    ! [A_89] :
      ( r2_hidden('#skF_3'(A_89),k2_relat_1(A_89))
      | v3_relat_1(A_89)
      | ~ v1_relat_1(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_206,plain,(
    ! [A_89] :
      ( m1_subset_1('#skF_3'(A_89),k2_relat_1(A_89))
      | v3_relat_1(A_89)
      | ~ v1_relat_1(A_89) ) ),
    inference(resolution,[status(thm)],[c_202,c_12])).

tff(c_149,plain,(
    ! [C_71,B_72,A_73] :
      ( v5_relat_1(C_71,B_72)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_73,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_157,plain,(
    v5_relat_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_149])).

tff(c_20,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k2_relat_1(B_17),A_16)
      | ~ v5_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_207,plain,(
    ! [C_90,B_91,A_92] :
      ( r2_hidden(C_90,B_91)
      | ~ r2_hidden(C_90,A_92)
      | ~ r1_tarski(A_92,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_384,plain,(
    ! [A_115,B_116,B_117] :
      ( r2_hidden('#skF_1'(A_115,B_116),B_117)
      | ~ r1_tarski(A_115,B_117)
      | r1_tarski(A_115,B_116) ) ),
    inference(resolution,[status(thm)],[c_6,c_207])).

tff(c_408,plain,(
    ! [A_120,B_121,B_122] :
      ( m1_subset_1('#skF_1'(A_120,B_121),B_122)
      | ~ r1_tarski(A_120,B_122)
      | r1_tarski(A_120,B_121) ) ),
    inference(resolution,[status(thm)],[c_384,c_12])).

tff(c_87,plain,(
    ! [A_59,B_60] :
      ( r2_hidden('#skF_1'(A_59,B_60),A_59)
      | r1_tarski(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_96,plain,(
    ! [B_60] :
      ( ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_4','#skF_5','#skF_6'),B_60),'#skF_5')
      | r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),B_60) ) ),
    inference(resolution,[status(thm)],[c_87,c_42])).

tff(c_301,plain,(
    ! [B_60] :
      ( ~ m1_subset_1('#skF_1'(k2_relat_1('#skF_6'),B_60),'#skF_5')
      | r1_tarski(k2_relat_1('#skF_6'),B_60) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_299,c_96])).

tff(c_445,plain,(
    ! [B_121] :
      ( ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5')
      | r1_tarski(k2_relat_1('#skF_6'),B_121) ) ),
    inference(resolution,[status(thm)],[c_408,c_301])).

tff(c_454,plain,(
    ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_445])).

tff(c_466,plain,
    ( ~ v5_relat_1('#skF_6','#skF_5')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_20,c_454])).

tff(c_470,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_157,c_466])).

tff(c_474,plain,(
    ! [B_125] : r1_tarski(k2_relat_1('#skF_6'),B_125) ),
    inference(splitRight,[status(thm)],[c_445])).

tff(c_215,plain,(
    ! [A_11,B_91,B_12] :
      ( r2_hidden(A_11,B_91)
      | ~ r1_tarski(B_12,B_91)
      | ~ m1_subset_1(A_11,B_12) ) ),
    inference(resolution,[status(thm)],[c_108,c_207])).

tff(c_487,plain,(
    ! [A_127,B_128] :
      ( r2_hidden(A_127,B_128)
      | ~ m1_subset_1(A_127,k2_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_474,c_215])).

tff(c_496,plain,(
    ! [B_128] :
      ( r2_hidden('#skF_3'('#skF_6'),B_128)
      | v3_relat_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_206,c_487])).

tff(c_509,plain,(
    ! [B_128] :
      ( r2_hidden('#skF_3'('#skF_6'),B_128)
      | v3_relat_1('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_496])).

tff(c_532,plain,(
    ! [B_131] : r2_hidden('#skF_3'('#skF_6'),B_131) ),
    inference(negUnitSimplification,[status(thm)],[c_363,c_509])).

tff(c_552,plain,(
    ! [B_131] : m1_subset_1('#skF_3'('#skF_6'),B_131) ),
    inference(resolution,[status(thm)],[c_532,c_12])).

tff(c_32,plain,(
    ! [A_22] :
      ( r2_hidden('#skF_3'(A_22),k2_relat_1(A_22))
      | v3_relat_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_309,plain,(
    ! [D_110] :
      ( ~ r2_hidden(D_110,k2_relat_1('#skF_6'))
      | ~ m1_subset_1(D_110,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_42])).

tff(c_313,plain,
    ( ~ m1_subset_1('#skF_3'('#skF_6'),'#skF_5')
    | v3_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_32,c_309])).

tff(c_324,plain,
    ( ~ m1_subset_1('#skF_3'('#skF_6'),'#skF_5')
    | v3_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_313])).

tff(c_327,plain,(
    ~ m1_subset_1('#skF_3'('#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_324])).

tff(c_560,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_552,c_327])).

tff(c_562,plain,(
    v3_relat_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_361])).

tff(c_355,plain,(
    ! [A_112] :
      ( m1_subset_1(k1_xboole_0,k2_relat_1(A_112))
      | ~ v3_relat_1(A_112)
      | ~ v1_relat_1(A_112) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_346,c_10])).

tff(c_577,plain,(
    ! [A_135,B_136,B_137] :
      ( r2_hidden('#skF_1'(A_135,B_136),B_137)
      | ~ r1_tarski(A_135,B_137)
      | r1_tarski(A_135,B_136) ) ),
    inference(resolution,[status(thm)],[c_6,c_207])).

tff(c_601,plain,(
    ! [A_140,B_141,B_142] :
      ( m1_subset_1('#skF_1'(A_140,B_141),B_142)
      | ~ r1_tarski(A_140,B_142)
      | r1_tarski(A_140,B_141) ) ),
    inference(resolution,[status(thm)],[c_577,c_12])).

tff(c_638,plain,(
    ! [B_141] :
      ( ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5')
      | r1_tarski(k2_relat_1('#skF_6'),B_141) ) ),
    inference(resolution,[status(thm)],[c_601,c_301])).

tff(c_647,plain,(
    ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_638])).

tff(c_659,plain,
    ( ~ v5_relat_1('#skF_6','#skF_5')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_20,c_647])).

tff(c_663,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_157,c_659])).

tff(c_667,plain,(
    ! [B_145] : r1_tarski(k2_relat_1('#skF_6'),B_145) ),
    inference(splitRight,[status(thm)],[c_638])).

tff(c_680,plain,(
    ! [A_147,B_148] :
      ( r2_hidden(A_147,B_148)
      | ~ m1_subset_1(A_147,k2_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_667,c_215])).

tff(c_686,plain,(
    ! [B_148] :
      ( r2_hidden(k1_xboole_0,B_148)
      | ~ v3_relat_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_355,c_680])).

tff(c_724,plain,(
    ! [B_151] : r2_hidden(k1_xboole_0,B_151) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_562,c_686])).

tff(c_743,plain,(
    ! [B_151] : m1_subset_1(k1_xboole_0,B_151) ),
    inference(resolution,[status(thm)],[c_724,c_12])).

tff(c_561,plain,(
    ~ m1_subset_1(k1_xboole_0,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_361])).

tff(c_747,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_743,c_561])).

tff(c_748,plain,(
    v3_relat_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_324])).

tff(c_768,plain,(
    ! [A_153] :
      ( '#skF_2'(k2_relat_1(A_153)) = k1_xboole_0
      | ~ v3_relat_1(A_153)
      | ~ v1_relat_1(A_153) ) ),
    inference(resolution,[status(thm)],[c_10,c_271])).

tff(c_777,plain,(
    ! [A_153] :
      ( m1_subset_1(k1_xboole_0,k2_relat_1(A_153))
      | ~ v3_relat_1(A_153)
      | ~ v1_relat_1(A_153) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_768,c_10])).

tff(c_799,plain,(
    ! [A_156,B_157,B_158] :
      ( r2_hidden('#skF_1'(A_156,B_157),B_158)
      | ~ r1_tarski(A_156,B_158)
      | r1_tarski(A_156,B_157) ) ),
    inference(resolution,[status(thm)],[c_6,c_207])).

tff(c_829,plain,(
    ! [A_163,B_164,B_165] :
      ( m1_subset_1('#skF_1'(A_163,B_164),B_165)
      | ~ r1_tarski(A_163,B_165)
      | r1_tarski(A_163,B_164) ) ),
    inference(resolution,[status(thm)],[c_799,c_12])).

tff(c_870,plain,(
    ! [B_164] :
      ( ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5')
      | r1_tarski(k2_relat_1('#skF_6'),B_164) ) ),
    inference(resolution,[status(thm)],[c_829,c_301])).

tff(c_879,plain,(
    ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_870])).

tff(c_900,plain,
    ( ~ v5_relat_1('#skF_6','#skF_5')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_20,c_879])).

tff(c_904,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_157,c_900])).

tff(c_908,plain,(
    ! [B_168] : r1_tarski(k2_relat_1('#skF_6'),B_168) ),
    inference(splitRight,[status(thm)],[c_870])).

tff(c_938,plain,(
    ! [A_172,B_173] :
      ( r2_hidden(A_172,B_173)
      | ~ m1_subset_1(A_172,k2_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_908,c_215])).

tff(c_944,plain,(
    ! [B_173] :
      ( r2_hidden(k1_xboole_0,B_173)
      | ~ v3_relat_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_777,c_938])).

tff(c_964,plain,(
    ! [B_174] : r2_hidden(k1_xboole_0,B_174) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_748,c_944])).

tff(c_983,plain,(
    ! [B_174] : m1_subset_1(k1_xboole_0,B_174) ),
    inference(resolution,[status(thm)],[c_964,c_12])).

tff(c_774,plain,
    ( ~ m1_subset_1(k1_xboole_0,'#skF_5')
    | ~ v3_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_768,c_302])).

tff(c_783,plain,(
    ~ m1_subset_1(k1_xboole_0,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_748,c_774])).

tff(c_987,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_983,c_783])).

tff(c_988,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_1228,plain,(
    ! [A_222,B_223,C_224] :
      ( k1_relset_1(A_222,B_223,C_224) = k1_relat_1(C_224)
      | ~ m1_subset_1(C_224,k1_zfmisc_1(k2_zfmisc_1(A_222,B_223))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1241,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_1228])).

tff(c_1243,plain,(
    k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1241,c_44])).

tff(c_1083,plain,(
    ! [C_193,B_194,A_195] :
      ( v5_relat_1(C_193,B_194)
      | ~ m1_subset_1(C_193,k1_zfmisc_1(k2_zfmisc_1(A_195,B_194))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1096,plain,(
    v5_relat_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_1083])).

tff(c_1104,plain,(
    ! [C_199,B_200,A_201] :
      ( r2_hidden(C_199,B_200)
      | ~ r2_hidden(C_199,A_201)
      | ~ r1_tarski(A_201,B_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1248,plain,(
    ! [A_225,B_226,B_227] :
      ( r2_hidden('#skF_1'(A_225,B_226),B_227)
      | ~ r1_tarski(A_225,B_227)
      | r1_tarski(A_225,B_226) ) ),
    inference(resolution,[status(thm)],[c_6,c_1104])).

tff(c_1278,plain,(
    ! [A_232,B_233,B_234] :
      ( m1_subset_1('#skF_1'(A_232,B_233),B_234)
      | ~ r1_tarski(A_232,B_234)
      | r1_tarski(A_232,B_233) ) ),
    inference(resolution,[status(thm)],[c_1248,c_12])).

tff(c_1167,plain,(
    ! [A_216,B_217,C_218] :
      ( k2_relset_1(A_216,B_217,C_218) = k2_relat_1(C_218)
      | ~ m1_subset_1(C_218,k1_zfmisc_1(k2_zfmisc_1(A_216,B_217))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1180,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_1167])).

tff(c_998,plain,(
    ! [A_175,B_176] :
      ( r2_hidden('#skF_1'(A_175,B_176),A_175)
      | r1_tarski(A_175,B_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1007,plain,(
    ! [B_176] :
      ( ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_4','#skF_5','#skF_6'),B_176),'#skF_5')
      | r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),B_176) ) ),
    inference(resolution,[status(thm)],[c_998,c_42])).

tff(c_1184,plain,(
    ! [B_176] :
      ( ~ m1_subset_1('#skF_1'(k2_relat_1('#skF_6'),B_176),'#skF_5')
      | r1_tarski(k2_relat_1('#skF_6'),B_176) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1180,c_1180,c_1007])).

tff(c_1317,plain,(
    ! [B_233] :
      ( ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5')
      | r1_tarski(k2_relat_1('#skF_6'),B_233) ) ),
    inference(resolution,[status(thm)],[c_1278,c_1184])).

tff(c_1323,plain,(
    ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1317])).

tff(c_1344,plain,
    ( ~ v5_relat_1('#skF_6','#skF_5')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_20,c_1323])).

tff(c_1348,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1055,c_1096,c_1344])).

tff(c_1352,plain,(
    ! [B_237] : r1_tarski(k2_relat_1('#skF_6'),B_237) ),
    inference(splitRight,[status(thm)],[c_1317])).

tff(c_1112,plain,(
    ! [A_11,B_200,B_12] :
      ( r2_hidden(A_11,B_200)
      | ~ r1_tarski(B_12,B_200)
      | v1_xboole_0(B_12)
      | ~ m1_subset_1(A_11,B_12) ) ),
    inference(resolution,[status(thm)],[c_14,c_1104])).

tff(c_1358,plain,(
    ! [A_11,B_237] :
      ( r2_hidden(A_11,B_237)
      | v1_xboole_0(k2_relat_1('#skF_6'))
      | ~ m1_subset_1(A_11,k2_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_1352,c_1112])).

tff(c_1382,plain,(
    v1_xboole_0(k2_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1358])).

tff(c_26,plain,(
    ! [A_21] :
      ( ~ v1_xboole_0(k2_relat_1(A_21))
      | ~ v1_relat_1(A_21)
      | v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1385,plain,
    ( ~ v1_relat_1('#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_1382,c_26])).

tff(c_1394,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1055,c_1385])).

tff(c_58,plain,(
    ! [A_51] :
      ( k1_relat_1(A_51) = k1_xboole_0
      | ~ v1_xboole_0(A_51) ) ),
    inference(resolution,[status(thm)],[c_54,c_8])).

tff(c_1399,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1394,c_58])).

tff(c_1406,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1243,c_1399])).

tff(c_1427,plain,(
    ! [A_243,B_244] :
      ( r2_hidden(A_243,B_244)
      | ~ m1_subset_1(A_243,k2_relat_1('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_1358])).

tff(c_1447,plain,(
    ! [B_245] : r2_hidden('#skF_2'(k2_relat_1('#skF_6')),B_245) ),
    inference(resolution,[status(thm)],[c_10,c_1427])).

tff(c_1465,plain,(
    ! [B_245] : m1_subset_1('#skF_2'(k2_relat_1('#skF_6')),B_245) ),
    inference(resolution,[status(thm)],[c_1447,c_12])).

tff(c_1022,plain,(
    ! [A_177,B_178] :
      ( r2_hidden(A_177,B_178)
      | v1_xboole_0(B_178)
      | ~ m1_subset_1(A_177,B_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1031,plain,(
    ! [A_177] :
      ( ~ m1_subset_1(A_177,'#skF_5')
      | v1_xboole_0(k2_relset_1('#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1(A_177,k2_relset_1('#skF_4','#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_1022,c_42])).

tff(c_1126,plain,(
    ! [A_207] :
      ( ~ m1_subset_1(A_207,'#skF_5')
      | ~ m1_subset_1(A_207,k2_relset_1('#skF_4','#skF_5','#skF_6')) ) ),
    inference(splitLeft,[status(thm)],[c_1031])).

tff(c_1136,plain,(
    ~ m1_subset_1('#skF_2'(k2_relset_1('#skF_4','#skF_5','#skF_6')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_1126])).

tff(c_1182,plain,(
    ~ m1_subset_1('#skF_2'(k2_relat_1('#skF_6')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1180,c_1136])).

tff(c_1468,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1465,c_1182])).

tff(c_1469,plain,(
    v1_xboole_0(k2_relset_1('#skF_4','#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_1031])).

tff(c_1477,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1469,c_8])).

tff(c_1671,plain,(
    ! [A_285,B_286,C_287] :
      ( k2_relset_1(A_285,B_286,C_287) = k2_relat_1(C_287)
      | ~ m1_subset_1(C_287,k1_zfmisc_1(k2_zfmisc_1(A_285,B_286))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1682,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_1671])).

tff(c_1690,plain,(
    k2_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1477,c_1682])).

tff(c_1713,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1690,c_26])).

tff(c_1729,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1055,c_988,c_1713])).

tff(c_1733,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1729,c_58])).

tff(c_1740,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1657,c_1733])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:56:47 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.47/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.61/1.54  
% 3.61/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.61/1.55  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v3_relat_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 3.61/1.55  
% 3.61/1.55  %Foreground sorts:
% 3.61/1.55  
% 3.61/1.55  
% 3.61/1.55  %Background operators:
% 3.61/1.55  
% 3.61/1.55  
% 3.61/1.55  %Foreground operators:
% 3.61/1.55  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.61/1.55  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.61/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.61/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.61/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.61/1.55  tff(v3_relat_1, type, v3_relat_1: $i > $o).
% 3.61/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.61/1.55  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.61/1.55  tff('#skF_5', type, '#skF_5': $i).
% 3.61/1.55  tff('#skF_6', type, '#skF_6': $i).
% 3.61/1.55  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.61/1.55  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.61/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.61/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.61/1.55  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.61/1.55  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.61/1.55  tff('#skF_4', type, '#skF_4': $i).
% 3.61/1.55  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.61/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.61/1.55  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.61/1.55  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.61/1.55  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.61/1.55  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.61/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.61/1.55  
% 3.61/1.58  tff(f_120, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_relset_1)).
% 3.61/1.58  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.61/1.58  tff(f_68, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.61/1.58  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.61/1.58  tff(f_39, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 3.61/1.58  tff(f_66, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_relat_1)).
% 3.61/1.58  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.61/1.58  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.61/1.58  tff(f_85, axiom, (![A]: (v1_relat_1(A) => (v3_relat_1(A) <=> (![B]: (r2_hidden(B, k2_relat_1(A)) => (B = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t184_relat_1)).
% 3.61/1.58  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.61/1.58  tff(f_43, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 3.61/1.58  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.61/1.58  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.61/1.58  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.61/1.58  tff(f_76, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 3.61/1.58  tff(c_46, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.61/1.58  tff(c_1637, plain, (![A_280, B_281, C_282]: (k1_relset_1(A_280, B_281, C_282)=k1_relat_1(C_282) | ~m1_subset_1(C_282, k1_zfmisc_1(k2_zfmisc_1(A_280, B_281))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.61/1.58  tff(c_1655, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_46, c_1637])).
% 3.61/1.58  tff(c_44, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.61/1.58  tff(c_1657, plain, (k1_relat_1('#skF_6')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1655, c_44])).
% 3.61/1.58  tff(c_24, plain, (![A_19, B_20]: (v1_relat_1(k2_zfmisc_1(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.61/1.58  tff(c_1045, plain, (![B_183, A_184]: (v1_relat_1(B_183) | ~m1_subset_1(B_183, k1_zfmisc_1(A_184)) | ~v1_relat_1(A_184))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.61/1.58  tff(c_1048, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_46, c_1045])).
% 3.61/1.58  tff(c_1055, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1048])).
% 3.61/1.58  tff(c_137, plain, (![B_69, A_70]: (v1_relat_1(B_69) | ~m1_subset_1(B_69, k1_zfmisc_1(A_70)) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.61/1.58  tff(c_140, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_46, c_137])).
% 3.61/1.58  tff(c_147, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_140])).
% 3.61/1.58  tff(c_10, plain, (![A_7]: (m1_subset_1('#skF_2'(A_7), A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.61/1.58  tff(c_22, plain, (![A_18]: (v1_xboole_0(k1_relat_1(A_18)) | ~v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.61/1.58  tff(c_54, plain, (![A_51]: (v1_xboole_0(k1_relat_1(A_51)) | ~v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.61/1.58  tff(c_8, plain, (![A_6]: (k1_xboole_0=A_6 | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.61/1.58  tff(c_59, plain, (![A_52]: (k1_relat_1(A_52)=k1_xboole_0 | ~v1_xboole_0(A_52))), inference(resolution, [status(thm)], [c_54, c_8])).
% 3.61/1.58  tff(c_66, plain, (![A_56]: (k1_relat_1(k1_relat_1(A_56))=k1_xboole_0 | ~v1_xboole_0(A_56))), inference(resolution, [status(thm)], [c_22, c_59])).
% 3.61/1.58  tff(c_75, plain, (![A_56]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(k1_relat_1(A_56)) | ~v1_xboole_0(A_56))), inference(superposition, [status(thm), theory('equality')], [c_66, c_22])).
% 3.61/1.58  tff(c_97, plain, (![A_61]: (~v1_xboole_0(k1_relat_1(A_61)) | ~v1_xboole_0(A_61))), inference(splitLeft, [status(thm)], [c_75])).
% 3.61/1.58  tff(c_104, plain, (![A_18]: (~v1_xboole_0(A_18))), inference(resolution, [status(thm)], [c_22, c_97])).
% 3.61/1.58  tff(c_14, plain, (![A_11, B_12]: (r2_hidden(A_11, B_12) | v1_xboole_0(B_12) | ~m1_subset_1(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.61/1.58  tff(c_108, plain, (![A_11, B_12]: (r2_hidden(A_11, B_12) | ~m1_subset_1(A_11, B_12))), inference(negUnitSimplification, [status(thm)], [c_104, c_14])).
% 3.61/1.58  tff(c_236, plain, (![B_100, A_101]: (k1_xboole_0=B_100 | ~r2_hidden(B_100, k2_relat_1(A_101)) | ~v3_relat_1(A_101) | ~v1_relat_1(A_101))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.61/1.58  tff(c_271, plain, (![A_105, A_106]: (k1_xboole_0=A_105 | ~v3_relat_1(A_106) | ~v1_relat_1(A_106) | ~m1_subset_1(A_105, k2_relat_1(A_106)))), inference(resolution, [status(thm)], [c_108, c_236])).
% 3.61/1.58  tff(c_346, plain, (![A_112]: ('#skF_2'(k2_relat_1(A_112))=k1_xboole_0 | ~v3_relat_1(A_112) | ~v1_relat_1(A_112))), inference(resolution, [status(thm)], [c_10, c_271])).
% 3.61/1.58  tff(c_286, plain, (![A_107, B_108, C_109]: (k2_relset_1(A_107, B_108, C_109)=k2_relat_1(C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.61/1.58  tff(c_299, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_46, c_286])).
% 3.61/1.58  tff(c_109, plain, (![A_63, B_64]: (r2_hidden(A_63, B_64) | ~m1_subset_1(A_63, B_64))), inference(negUnitSimplification, [status(thm)], [c_104, c_14])).
% 3.61/1.58  tff(c_42, plain, (![D_46]: (~r2_hidden(D_46, k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1(D_46, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.61/1.58  tff(c_119, plain, (![A_65]: (~m1_subset_1(A_65, '#skF_5') | ~m1_subset_1(A_65, k2_relset_1('#skF_4', '#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_109, c_42])).
% 3.61/1.58  tff(c_124, plain, (~m1_subset_1('#skF_2'(k2_relset_1('#skF_4', '#skF_5', '#skF_6')), '#skF_5')), inference(resolution, [status(thm)], [c_10, c_119])).
% 3.61/1.58  tff(c_302, plain, (~m1_subset_1('#skF_2'(k2_relat_1('#skF_6')), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_299, c_124])).
% 3.61/1.58  tff(c_352, plain, (~m1_subset_1(k1_xboole_0, '#skF_5') | ~v3_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_346, c_302])).
% 3.61/1.58  tff(c_361, plain, (~m1_subset_1(k1_xboole_0, '#skF_5') | ~v3_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_147, c_352])).
% 3.61/1.58  tff(c_363, plain, (~v3_relat_1('#skF_6')), inference(splitLeft, [status(thm)], [c_361])).
% 3.61/1.58  tff(c_202, plain, (![A_89]: (r2_hidden('#skF_3'(A_89), k2_relat_1(A_89)) | v3_relat_1(A_89) | ~v1_relat_1(A_89))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.61/1.58  tff(c_12, plain, (![A_9, B_10]: (m1_subset_1(A_9, B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.61/1.58  tff(c_206, plain, (![A_89]: (m1_subset_1('#skF_3'(A_89), k2_relat_1(A_89)) | v3_relat_1(A_89) | ~v1_relat_1(A_89))), inference(resolution, [status(thm)], [c_202, c_12])).
% 3.61/1.58  tff(c_149, plain, (![C_71, B_72, A_73]: (v5_relat_1(C_71, B_72) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_73, B_72))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.61/1.58  tff(c_157, plain, (v5_relat_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_46, c_149])).
% 3.61/1.58  tff(c_20, plain, (![B_17, A_16]: (r1_tarski(k2_relat_1(B_17), A_16) | ~v5_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.61/1.58  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.61/1.58  tff(c_207, plain, (![C_90, B_91, A_92]: (r2_hidden(C_90, B_91) | ~r2_hidden(C_90, A_92) | ~r1_tarski(A_92, B_91))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.61/1.58  tff(c_384, plain, (![A_115, B_116, B_117]: (r2_hidden('#skF_1'(A_115, B_116), B_117) | ~r1_tarski(A_115, B_117) | r1_tarski(A_115, B_116))), inference(resolution, [status(thm)], [c_6, c_207])).
% 3.61/1.58  tff(c_408, plain, (![A_120, B_121, B_122]: (m1_subset_1('#skF_1'(A_120, B_121), B_122) | ~r1_tarski(A_120, B_122) | r1_tarski(A_120, B_121))), inference(resolution, [status(thm)], [c_384, c_12])).
% 3.61/1.58  tff(c_87, plain, (![A_59, B_60]: (r2_hidden('#skF_1'(A_59, B_60), A_59) | r1_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.61/1.58  tff(c_96, plain, (![B_60]: (~m1_subset_1('#skF_1'(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), B_60), '#skF_5') | r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), B_60))), inference(resolution, [status(thm)], [c_87, c_42])).
% 3.61/1.58  tff(c_301, plain, (![B_60]: (~m1_subset_1('#skF_1'(k2_relat_1('#skF_6'), B_60), '#skF_5') | r1_tarski(k2_relat_1('#skF_6'), B_60))), inference(demodulation, [status(thm), theory('equality')], [c_299, c_299, c_96])).
% 3.61/1.58  tff(c_445, plain, (![B_121]: (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5') | r1_tarski(k2_relat_1('#skF_6'), B_121))), inference(resolution, [status(thm)], [c_408, c_301])).
% 3.61/1.58  tff(c_454, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5')), inference(splitLeft, [status(thm)], [c_445])).
% 3.61/1.58  tff(c_466, plain, (~v5_relat_1('#skF_6', '#skF_5') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_20, c_454])).
% 3.61/1.58  tff(c_470, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_147, c_157, c_466])).
% 3.61/1.58  tff(c_474, plain, (![B_125]: (r1_tarski(k2_relat_1('#skF_6'), B_125))), inference(splitRight, [status(thm)], [c_445])).
% 3.61/1.58  tff(c_215, plain, (![A_11, B_91, B_12]: (r2_hidden(A_11, B_91) | ~r1_tarski(B_12, B_91) | ~m1_subset_1(A_11, B_12))), inference(resolution, [status(thm)], [c_108, c_207])).
% 3.61/1.58  tff(c_487, plain, (![A_127, B_128]: (r2_hidden(A_127, B_128) | ~m1_subset_1(A_127, k2_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_474, c_215])).
% 3.61/1.58  tff(c_496, plain, (![B_128]: (r2_hidden('#skF_3'('#skF_6'), B_128) | v3_relat_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_206, c_487])).
% 3.61/1.58  tff(c_509, plain, (![B_128]: (r2_hidden('#skF_3'('#skF_6'), B_128) | v3_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_147, c_496])).
% 3.61/1.58  tff(c_532, plain, (![B_131]: (r2_hidden('#skF_3'('#skF_6'), B_131))), inference(negUnitSimplification, [status(thm)], [c_363, c_509])).
% 3.61/1.58  tff(c_552, plain, (![B_131]: (m1_subset_1('#skF_3'('#skF_6'), B_131))), inference(resolution, [status(thm)], [c_532, c_12])).
% 3.61/1.58  tff(c_32, plain, (![A_22]: (r2_hidden('#skF_3'(A_22), k2_relat_1(A_22)) | v3_relat_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.61/1.58  tff(c_309, plain, (![D_110]: (~r2_hidden(D_110, k2_relat_1('#skF_6')) | ~m1_subset_1(D_110, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_299, c_42])).
% 3.61/1.58  tff(c_313, plain, (~m1_subset_1('#skF_3'('#skF_6'), '#skF_5') | v3_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_32, c_309])).
% 3.61/1.58  tff(c_324, plain, (~m1_subset_1('#skF_3'('#skF_6'), '#skF_5') | v3_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_147, c_313])).
% 3.61/1.58  tff(c_327, plain, (~m1_subset_1('#skF_3'('#skF_6'), '#skF_5')), inference(splitLeft, [status(thm)], [c_324])).
% 3.61/1.58  tff(c_560, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_552, c_327])).
% 3.61/1.58  tff(c_562, plain, (v3_relat_1('#skF_6')), inference(splitRight, [status(thm)], [c_361])).
% 3.61/1.58  tff(c_355, plain, (![A_112]: (m1_subset_1(k1_xboole_0, k2_relat_1(A_112)) | ~v3_relat_1(A_112) | ~v1_relat_1(A_112))), inference(superposition, [status(thm), theory('equality')], [c_346, c_10])).
% 3.61/1.58  tff(c_577, plain, (![A_135, B_136, B_137]: (r2_hidden('#skF_1'(A_135, B_136), B_137) | ~r1_tarski(A_135, B_137) | r1_tarski(A_135, B_136))), inference(resolution, [status(thm)], [c_6, c_207])).
% 3.61/1.58  tff(c_601, plain, (![A_140, B_141, B_142]: (m1_subset_1('#skF_1'(A_140, B_141), B_142) | ~r1_tarski(A_140, B_142) | r1_tarski(A_140, B_141))), inference(resolution, [status(thm)], [c_577, c_12])).
% 3.61/1.58  tff(c_638, plain, (![B_141]: (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5') | r1_tarski(k2_relat_1('#skF_6'), B_141))), inference(resolution, [status(thm)], [c_601, c_301])).
% 3.61/1.58  tff(c_647, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5')), inference(splitLeft, [status(thm)], [c_638])).
% 3.61/1.58  tff(c_659, plain, (~v5_relat_1('#skF_6', '#skF_5') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_20, c_647])).
% 3.61/1.58  tff(c_663, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_147, c_157, c_659])).
% 3.61/1.58  tff(c_667, plain, (![B_145]: (r1_tarski(k2_relat_1('#skF_6'), B_145))), inference(splitRight, [status(thm)], [c_638])).
% 3.61/1.58  tff(c_680, plain, (![A_147, B_148]: (r2_hidden(A_147, B_148) | ~m1_subset_1(A_147, k2_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_667, c_215])).
% 3.61/1.58  tff(c_686, plain, (![B_148]: (r2_hidden(k1_xboole_0, B_148) | ~v3_relat_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_355, c_680])).
% 3.61/1.58  tff(c_724, plain, (![B_151]: (r2_hidden(k1_xboole_0, B_151))), inference(demodulation, [status(thm), theory('equality')], [c_147, c_562, c_686])).
% 3.61/1.58  tff(c_743, plain, (![B_151]: (m1_subset_1(k1_xboole_0, B_151))), inference(resolution, [status(thm)], [c_724, c_12])).
% 3.61/1.58  tff(c_561, plain, (~m1_subset_1(k1_xboole_0, '#skF_5')), inference(splitRight, [status(thm)], [c_361])).
% 3.61/1.58  tff(c_747, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_743, c_561])).
% 3.61/1.58  tff(c_748, plain, (v3_relat_1('#skF_6')), inference(splitRight, [status(thm)], [c_324])).
% 3.61/1.58  tff(c_768, plain, (![A_153]: ('#skF_2'(k2_relat_1(A_153))=k1_xboole_0 | ~v3_relat_1(A_153) | ~v1_relat_1(A_153))), inference(resolution, [status(thm)], [c_10, c_271])).
% 3.61/1.58  tff(c_777, plain, (![A_153]: (m1_subset_1(k1_xboole_0, k2_relat_1(A_153)) | ~v3_relat_1(A_153) | ~v1_relat_1(A_153))), inference(superposition, [status(thm), theory('equality')], [c_768, c_10])).
% 3.61/1.58  tff(c_799, plain, (![A_156, B_157, B_158]: (r2_hidden('#skF_1'(A_156, B_157), B_158) | ~r1_tarski(A_156, B_158) | r1_tarski(A_156, B_157))), inference(resolution, [status(thm)], [c_6, c_207])).
% 3.61/1.58  tff(c_829, plain, (![A_163, B_164, B_165]: (m1_subset_1('#skF_1'(A_163, B_164), B_165) | ~r1_tarski(A_163, B_165) | r1_tarski(A_163, B_164))), inference(resolution, [status(thm)], [c_799, c_12])).
% 3.61/1.58  tff(c_870, plain, (![B_164]: (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5') | r1_tarski(k2_relat_1('#skF_6'), B_164))), inference(resolution, [status(thm)], [c_829, c_301])).
% 3.61/1.58  tff(c_879, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5')), inference(splitLeft, [status(thm)], [c_870])).
% 3.61/1.58  tff(c_900, plain, (~v5_relat_1('#skF_6', '#skF_5') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_20, c_879])).
% 3.61/1.58  tff(c_904, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_147, c_157, c_900])).
% 3.61/1.58  tff(c_908, plain, (![B_168]: (r1_tarski(k2_relat_1('#skF_6'), B_168))), inference(splitRight, [status(thm)], [c_870])).
% 3.61/1.58  tff(c_938, plain, (![A_172, B_173]: (r2_hidden(A_172, B_173) | ~m1_subset_1(A_172, k2_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_908, c_215])).
% 3.61/1.58  tff(c_944, plain, (![B_173]: (r2_hidden(k1_xboole_0, B_173) | ~v3_relat_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_777, c_938])).
% 3.61/1.58  tff(c_964, plain, (![B_174]: (r2_hidden(k1_xboole_0, B_174))), inference(demodulation, [status(thm), theory('equality')], [c_147, c_748, c_944])).
% 3.61/1.58  tff(c_983, plain, (![B_174]: (m1_subset_1(k1_xboole_0, B_174))), inference(resolution, [status(thm)], [c_964, c_12])).
% 3.61/1.58  tff(c_774, plain, (~m1_subset_1(k1_xboole_0, '#skF_5') | ~v3_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_768, c_302])).
% 3.61/1.58  tff(c_783, plain, (~m1_subset_1(k1_xboole_0, '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_147, c_748, c_774])).
% 3.61/1.58  tff(c_987, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_983, c_783])).
% 3.61/1.58  tff(c_988, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_75])).
% 3.61/1.58  tff(c_1228, plain, (![A_222, B_223, C_224]: (k1_relset_1(A_222, B_223, C_224)=k1_relat_1(C_224) | ~m1_subset_1(C_224, k1_zfmisc_1(k2_zfmisc_1(A_222, B_223))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.61/1.58  tff(c_1241, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_46, c_1228])).
% 3.61/1.58  tff(c_1243, plain, (k1_relat_1('#skF_6')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1241, c_44])).
% 3.61/1.58  tff(c_1083, plain, (![C_193, B_194, A_195]: (v5_relat_1(C_193, B_194) | ~m1_subset_1(C_193, k1_zfmisc_1(k2_zfmisc_1(A_195, B_194))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.61/1.58  tff(c_1096, plain, (v5_relat_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_46, c_1083])).
% 3.61/1.58  tff(c_1104, plain, (![C_199, B_200, A_201]: (r2_hidden(C_199, B_200) | ~r2_hidden(C_199, A_201) | ~r1_tarski(A_201, B_200))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.61/1.58  tff(c_1248, plain, (![A_225, B_226, B_227]: (r2_hidden('#skF_1'(A_225, B_226), B_227) | ~r1_tarski(A_225, B_227) | r1_tarski(A_225, B_226))), inference(resolution, [status(thm)], [c_6, c_1104])).
% 3.61/1.58  tff(c_1278, plain, (![A_232, B_233, B_234]: (m1_subset_1('#skF_1'(A_232, B_233), B_234) | ~r1_tarski(A_232, B_234) | r1_tarski(A_232, B_233))), inference(resolution, [status(thm)], [c_1248, c_12])).
% 3.61/1.58  tff(c_1167, plain, (![A_216, B_217, C_218]: (k2_relset_1(A_216, B_217, C_218)=k2_relat_1(C_218) | ~m1_subset_1(C_218, k1_zfmisc_1(k2_zfmisc_1(A_216, B_217))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.61/1.58  tff(c_1180, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_46, c_1167])).
% 3.61/1.58  tff(c_998, plain, (![A_175, B_176]: (r2_hidden('#skF_1'(A_175, B_176), A_175) | r1_tarski(A_175, B_176))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.61/1.58  tff(c_1007, plain, (![B_176]: (~m1_subset_1('#skF_1'(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), B_176), '#skF_5') | r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), B_176))), inference(resolution, [status(thm)], [c_998, c_42])).
% 3.61/1.58  tff(c_1184, plain, (![B_176]: (~m1_subset_1('#skF_1'(k2_relat_1('#skF_6'), B_176), '#skF_5') | r1_tarski(k2_relat_1('#skF_6'), B_176))), inference(demodulation, [status(thm), theory('equality')], [c_1180, c_1180, c_1007])).
% 3.61/1.58  tff(c_1317, plain, (![B_233]: (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5') | r1_tarski(k2_relat_1('#skF_6'), B_233))), inference(resolution, [status(thm)], [c_1278, c_1184])).
% 3.61/1.58  tff(c_1323, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5')), inference(splitLeft, [status(thm)], [c_1317])).
% 3.61/1.58  tff(c_1344, plain, (~v5_relat_1('#skF_6', '#skF_5') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_20, c_1323])).
% 3.61/1.58  tff(c_1348, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1055, c_1096, c_1344])).
% 3.61/1.58  tff(c_1352, plain, (![B_237]: (r1_tarski(k2_relat_1('#skF_6'), B_237))), inference(splitRight, [status(thm)], [c_1317])).
% 3.61/1.58  tff(c_1112, plain, (![A_11, B_200, B_12]: (r2_hidden(A_11, B_200) | ~r1_tarski(B_12, B_200) | v1_xboole_0(B_12) | ~m1_subset_1(A_11, B_12))), inference(resolution, [status(thm)], [c_14, c_1104])).
% 3.61/1.58  tff(c_1358, plain, (![A_11, B_237]: (r2_hidden(A_11, B_237) | v1_xboole_0(k2_relat_1('#skF_6')) | ~m1_subset_1(A_11, k2_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_1352, c_1112])).
% 3.61/1.58  tff(c_1382, plain, (v1_xboole_0(k2_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_1358])).
% 3.61/1.58  tff(c_26, plain, (![A_21]: (~v1_xboole_0(k2_relat_1(A_21)) | ~v1_relat_1(A_21) | v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.61/1.58  tff(c_1385, plain, (~v1_relat_1('#skF_6') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_1382, c_26])).
% 3.61/1.58  tff(c_1394, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1055, c_1385])).
% 3.61/1.58  tff(c_58, plain, (![A_51]: (k1_relat_1(A_51)=k1_xboole_0 | ~v1_xboole_0(A_51))), inference(resolution, [status(thm)], [c_54, c_8])).
% 3.61/1.58  tff(c_1399, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_1394, c_58])).
% 3.61/1.58  tff(c_1406, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1243, c_1399])).
% 3.61/1.58  tff(c_1427, plain, (![A_243, B_244]: (r2_hidden(A_243, B_244) | ~m1_subset_1(A_243, k2_relat_1('#skF_6')))), inference(splitRight, [status(thm)], [c_1358])).
% 3.61/1.58  tff(c_1447, plain, (![B_245]: (r2_hidden('#skF_2'(k2_relat_1('#skF_6')), B_245))), inference(resolution, [status(thm)], [c_10, c_1427])).
% 3.61/1.58  tff(c_1465, plain, (![B_245]: (m1_subset_1('#skF_2'(k2_relat_1('#skF_6')), B_245))), inference(resolution, [status(thm)], [c_1447, c_12])).
% 3.61/1.58  tff(c_1022, plain, (![A_177, B_178]: (r2_hidden(A_177, B_178) | v1_xboole_0(B_178) | ~m1_subset_1(A_177, B_178))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.61/1.58  tff(c_1031, plain, (![A_177]: (~m1_subset_1(A_177, '#skF_5') | v1_xboole_0(k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1(A_177, k2_relset_1('#skF_4', '#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_1022, c_42])).
% 3.61/1.58  tff(c_1126, plain, (![A_207]: (~m1_subset_1(A_207, '#skF_5') | ~m1_subset_1(A_207, k2_relset_1('#skF_4', '#skF_5', '#skF_6')))), inference(splitLeft, [status(thm)], [c_1031])).
% 3.61/1.58  tff(c_1136, plain, (~m1_subset_1('#skF_2'(k2_relset_1('#skF_4', '#skF_5', '#skF_6')), '#skF_5')), inference(resolution, [status(thm)], [c_10, c_1126])).
% 3.61/1.58  tff(c_1182, plain, (~m1_subset_1('#skF_2'(k2_relat_1('#skF_6')), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1180, c_1136])).
% 3.61/1.58  tff(c_1468, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1465, c_1182])).
% 3.61/1.58  tff(c_1469, plain, (v1_xboole_0(k2_relset_1('#skF_4', '#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_1031])).
% 3.61/1.58  tff(c_1477, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_1469, c_8])).
% 3.61/1.58  tff(c_1671, plain, (![A_285, B_286, C_287]: (k2_relset_1(A_285, B_286, C_287)=k2_relat_1(C_287) | ~m1_subset_1(C_287, k1_zfmisc_1(k2_zfmisc_1(A_285, B_286))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.61/1.58  tff(c_1682, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_46, c_1671])).
% 3.61/1.58  tff(c_1690, plain, (k2_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1477, c_1682])).
% 3.61/1.58  tff(c_1713, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_6') | v1_xboole_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1690, c_26])).
% 3.61/1.58  tff(c_1729, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1055, c_988, c_1713])).
% 3.61/1.58  tff(c_1733, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_1729, c_58])).
% 3.61/1.58  tff(c_1740, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1657, c_1733])).
% 3.61/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.61/1.58  
% 3.61/1.58  Inference rules
% 3.61/1.58  ----------------------
% 3.61/1.58  #Ref     : 0
% 3.61/1.58  #Sup     : 324
% 3.61/1.58  #Fact    : 0
% 3.61/1.58  #Define  : 0
% 3.61/1.58  #Split   : 14
% 3.61/1.58  #Chain   : 0
% 3.61/1.58  #Close   : 0
% 3.61/1.58  
% 3.61/1.58  Ordering : KBO
% 3.61/1.58  
% 3.61/1.58  Simplification rules
% 3.61/1.58  ----------------------
% 3.61/1.58  #Subsume      : 48
% 3.61/1.58  #Demod        : 115
% 3.61/1.58  #Tautology    : 87
% 3.61/1.58  #SimpNegUnit  : 7
% 3.61/1.58  #BackRed      : 18
% 3.61/1.58  
% 3.61/1.58  #Partial instantiations: 0
% 3.61/1.58  #Strategies tried      : 1
% 3.61/1.58  
% 3.61/1.58  Timing (in seconds)
% 3.61/1.58  ----------------------
% 3.61/1.58  Preprocessing        : 0.30
% 3.61/1.58  Parsing              : 0.16
% 3.61/1.58  CNF conversion       : 0.02
% 3.61/1.58  Main loop            : 0.52
% 3.61/1.58  Inferencing          : 0.20
% 3.61/1.58  Reduction            : 0.15
% 3.61/1.58  Demodulation         : 0.10
% 3.61/1.58  BG Simplification    : 0.02
% 3.61/1.58  Subsumption          : 0.09
% 3.61/1.58  Abstraction          : 0.03
% 3.61/1.58  MUC search           : 0.00
% 3.61/1.58  Cooper               : 0.00
% 3.61/1.58  Total                : 0.88
% 3.61/1.58  Index Insertion      : 0.00
% 3.61/1.58  Index Deletion       : 0.00
% 3.61/1.58  Index Matching       : 0.00
% 3.61/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
