%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:18 EST 2020

% Result     : Theorem 3.64s
% Output     : CNFRefutation 3.64s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 171 expanded)
%              Number of leaves         :   37 (  73 expanded)
%              Depth                    :   15
%              Number of atoms          :  176 ( 441 expanded)
%              Number of equality atoms :   26 (  59 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_136,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( v1_funct_1(B)
              & v1_funct_2(B,A,A)
              & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ! [C] :
                ( ( v1_relat_1(C)
                  & v5_relat_1(C,A)
                  & v1_funct_1(C) )
               => k1_relat_1(k5_relat_1(C,B)) = k1_relat_1(C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t200_funct_2)).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_116,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_108,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

tff(c_46,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_14,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_48,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_65,plain,(
    ! [B_44,A_45] :
      ( v1_relat_1(B_44)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_45))
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_68,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_48,c_65])).

tff(c_71,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_68])).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_77,plain,(
    ! [C_49,A_50,B_51] :
      ( v4_relat_1(C_49,A_50)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_81,plain,(
    v4_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_77])).

tff(c_140,plain,(
    ! [B_64,A_65] :
      ( k1_relat_1(B_64) = A_65
      | ~ v1_partfun1(B_64,A_65)
      | ~ v4_relat_1(B_64,A_65)
      | ~ v1_relat_1(B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_143,plain,
    ( k1_relat_1('#skF_2') = '#skF_1'
    | ~ v1_partfun1('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_81,c_140])).

tff(c_146,plain,
    ( k1_relat_1('#skF_2') = '#skF_1'
    | ~ v1_partfun1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_143])).

tff(c_147,plain,(
    ~ v1_partfun1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_146])).

tff(c_52,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_50,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_199,plain,(
    ! [C_75,A_76,B_77] :
      ( v1_partfun1(C_75,A_76)
      | ~ v1_funct_2(C_75,A_76,B_77)
      | ~ v1_funct_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77)))
      | v1_xboole_0(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_205,plain,
    ( v1_partfun1('#skF_2','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_199])).

tff(c_209,plain,
    ( v1_partfun1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_205])).

tff(c_211,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_147,c_209])).

tff(c_212,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_233,plain,(
    ! [A_79,B_80] :
      ( k10_relat_1(A_79,k1_relat_1(B_80)) = k1_relat_1(k5_relat_1(A_79,B_80))
      | ~ v1_relat_1(B_80)
      | ~ v1_relat_1(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_242,plain,(
    ! [A_79] :
      ( k1_relat_1(k5_relat_1(A_79,'#skF_2')) = k10_relat_1(A_79,'#skF_1')
      | ~ v1_relat_1('#skF_2')
      | ~ v1_relat_1(A_79) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_233])).

tff(c_247,plain,(
    ! [A_81] :
      ( k1_relat_1(k5_relat_1(A_81,'#skF_2')) = k10_relat_1(A_81,'#skF_1')
      | ~ v1_relat_1(A_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_242])).

tff(c_40,plain,(
    k1_relat_1(k5_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_269,plain,
    ( k10_relat_1('#skF_3','#skF_1') != k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_40])).

tff(c_279,plain,(
    k10_relat_1('#skF_3','#skF_1') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_269])).

tff(c_42,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_44,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_12,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_296,plain,(
    ! [C_83,A_84,B_85] :
      ( m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85)))
      | ~ r1_tarski(k2_relat_1(C_83),B_85)
      | ~ r1_tarski(k1_relat_1(C_83),A_84)
      | ~ v1_relat_1(C_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_28,plain,(
    ! [C_25,A_23,B_24] :
      ( v4_relat_1(C_25,A_23)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_620,plain,(
    ! [C_115,A_116,B_117] :
      ( v4_relat_1(C_115,A_116)
      | ~ r1_tarski(k2_relat_1(C_115),B_117)
      | ~ r1_tarski(k1_relat_1(C_115),A_116)
      | ~ v1_relat_1(C_115) ) ),
    inference(resolution,[status(thm)],[c_296,c_28])).

tff(c_641,plain,(
    ! [C_121,A_122] :
      ( v4_relat_1(C_121,A_122)
      | ~ r1_tarski(k1_relat_1(C_121),A_122)
      | ~ v1_relat_1(C_121) ) ),
    inference(resolution,[status(thm)],[c_6,c_620])).

tff(c_683,plain,(
    ! [C_124] :
      ( v4_relat_1(C_124,k1_relat_1(C_124))
      | ~ v1_relat_1(C_124) ) ),
    inference(resolution,[status(thm)],[c_6,c_641])).

tff(c_20,plain,(
    ! [B_16,A_15] :
      ( k7_relat_1(B_16,A_15) = B_16
      | ~ v4_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_730,plain,(
    ! [C_128] :
      ( k7_relat_1(C_128,k1_relat_1(C_128)) = C_128
      | ~ v1_relat_1(C_128) ) ),
    inference(resolution,[status(thm)],[c_683,c_20])).

tff(c_16,plain,(
    ! [B_11,A_10] :
      ( k2_relat_1(k7_relat_1(B_11,A_10)) = k9_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_736,plain,(
    ! [C_128] :
      ( k9_relat_1(C_128,k1_relat_1(C_128)) = k2_relat_1(C_128)
      | ~ v1_relat_1(C_128)
      | ~ v1_relat_1(C_128) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_730,c_16])).

tff(c_782,plain,(
    ! [A_131,C_132,B_133] :
      ( r1_tarski(A_131,k10_relat_1(C_132,B_133))
      | ~ r1_tarski(k9_relat_1(C_132,A_131),B_133)
      | ~ r1_tarski(A_131,k1_relat_1(C_132))
      | ~ v1_funct_1(C_132)
      | ~ v1_relat_1(C_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_785,plain,(
    ! [C_128,B_133] :
      ( r1_tarski(k1_relat_1(C_128),k10_relat_1(C_128,B_133))
      | ~ r1_tarski(k2_relat_1(C_128),B_133)
      | ~ r1_tarski(k1_relat_1(C_128),k1_relat_1(C_128))
      | ~ v1_funct_1(C_128)
      | ~ v1_relat_1(C_128)
      | ~ v1_relat_1(C_128)
      | ~ v1_relat_1(C_128) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_736,c_782])).

tff(c_1545,plain,(
    ! [C_173,B_174] :
      ( r1_tarski(k1_relat_1(C_173),k10_relat_1(C_173,B_174))
      | ~ r1_tarski(k2_relat_1(C_173),B_174)
      | ~ v1_funct_1(C_173)
      | ~ v1_relat_1(C_173) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_785])).

tff(c_22,plain,(
    ! [A_17,B_19] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_17,B_19)),k1_relat_1(A_17))
      | ~ v1_relat_1(B_19)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_260,plain,(
    ! [A_81] :
      ( r1_tarski(k10_relat_1(A_81,'#skF_1'),k1_relat_1(A_81))
      | ~ v1_relat_1('#skF_2')
      | ~ v1_relat_1(A_81)
      | ~ v1_relat_1(A_81) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_22])).

tff(c_284,plain,(
    ! [A_82] :
      ( r1_tarski(k10_relat_1(A_82,'#skF_1'),k1_relat_1(A_82))
      | ~ v1_relat_1(A_82) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_260])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_293,plain,(
    ! [A_82] :
      ( k10_relat_1(A_82,'#skF_1') = k1_relat_1(A_82)
      | ~ r1_tarski(k1_relat_1(A_82),k10_relat_1(A_82,'#skF_1'))
      | ~ v1_relat_1(A_82) ) ),
    inference(resolution,[status(thm)],[c_284,c_2])).

tff(c_1582,plain,(
    ! [C_175] :
      ( k10_relat_1(C_175,'#skF_1') = k1_relat_1(C_175)
      | ~ r1_tarski(k2_relat_1(C_175),'#skF_1')
      | ~ v1_funct_1(C_175)
      | ~ v1_relat_1(C_175) ) ),
    inference(resolution,[status(thm)],[c_1545,c_293])).

tff(c_1598,plain,(
    ! [B_176] :
      ( k10_relat_1(B_176,'#skF_1') = k1_relat_1(B_176)
      | ~ v1_funct_1(B_176)
      | ~ v5_relat_1(B_176,'#skF_1')
      | ~ v1_relat_1(B_176) ) ),
    inference(resolution,[status(thm)],[c_12,c_1582])).

tff(c_1608,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_1598])).

tff(c_1615,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_1608])).

tff(c_1617,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_279,c_1615])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:18:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.64/1.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.64/1.65  
% 3.64/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.64/1.66  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.64/1.66  
% 3.64/1.66  %Foreground sorts:
% 3.64/1.66  
% 3.64/1.66  
% 3.64/1.66  %Background operators:
% 3.64/1.66  
% 3.64/1.66  
% 3.64/1.66  %Foreground operators:
% 3.64/1.66  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.64/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.64/1.66  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.64/1.66  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.64/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.64/1.66  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.64/1.66  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.64/1.66  tff('#skF_2', type, '#skF_2': $i).
% 3.64/1.66  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.64/1.66  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.64/1.66  tff('#skF_3', type, '#skF_3': $i).
% 3.64/1.66  tff('#skF_1', type, '#skF_1': $i).
% 3.64/1.66  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.64/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.64/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.64/1.66  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.64/1.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.64/1.66  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.64/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.64/1.66  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.64/1.66  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.64/1.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.64/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.64/1.66  
% 3.64/1.67  tff(f_136, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (k1_relat_1(k5_relat_1(C, B)) = k1_relat_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t200_funct_2)).
% 3.64/1.67  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.64/1.67  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.64/1.67  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.64/1.67  tff(f_116, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 3.64/1.67  tff(f_108, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 3.64/1.67  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 3.64/1.67  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.64/1.67  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.64/1.67  tff(f_94, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 3.64/1.67  tff(f_63, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.64/1.67  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.64/1.67  tff(f_80, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 3.64/1.67  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_relat_1)).
% 3.64/1.67  tff(c_46, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.64/1.67  tff(c_14, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.64/1.67  tff(c_48, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.64/1.67  tff(c_65, plain, (![B_44, A_45]: (v1_relat_1(B_44) | ~m1_subset_1(B_44, k1_zfmisc_1(A_45)) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.64/1.67  tff(c_68, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_48, c_65])).
% 3.64/1.67  tff(c_71, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_68])).
% 3.64/1.67  tff(c_54, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.64/1.67  tff(c_77, plain, (![C_49, A_50, B_51]: (v4_relat_1(C_49, A_50) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.64/1.67  tff(c_81, plain, (v4_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_48, c_77])).
% 3.64/1.67  tff(c_140, plain, (![B_64, A_65]: (k1_relat_1(B_64)=A_65 | ~v1_partfun1(B_64, A_65) | ~v4_relat_1(B_64, A_65) | ~v1_relat_1(B_64))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.64/1.67  tff(c_143, plain, (k1_relat_1('#skF_2')='#skF_1' | ~v1_partfun1('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_81, c_140])).
% 3.64/1.67  tff(c_146, plain, (k1_relat_1('#skF_2')='#skF_1' | ~v1_partfun1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_143])).
% 3.64/1.67  tff(c_147, plain, (~v1_partfun1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_146])).
% 3.64/1.67  tff(c_52, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.64/1.67  tff(c_50, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.64/1.67  tff(c_199, plain, (![C_75, A_76, B_77]: (v1_partfun1(C_75, A_76) | ~v1_funct_2(C_75, A_76, B_77) | ~v1_funct_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))) | v1_xboole_0(B_77))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.64/1.67  tff(c_205, plain, (v1_partfun1('#skF_2', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_48, c_199])).
% 3.64/1.67  tff(c_209, plain, (v1_partfun1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_205])).
% 3.64/1.67  tff(c_211, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_147, c_209])).
% 3.64/1.67  tff(c_212, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_146])).
% 3.64/1.67  tff(c_233, plain, (![A_79, B_80]: (k10_relat_1(A_79, k1_relat_1(B_80))=k1_relat_1(k5_relat_1(A_79, B_80)) | ~v1_relat_1(B_80) | ~v1_relat_1(A_79))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.64/1.67  tff(c_242, plain, (![A_79]: (k1_relat_1(k5_relat_1(A_79, '#skF_2'))=k10_relat_1(A_79, '#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1(A_79))), inference(superposition, [status(thm), theory('equality')], [c_212, c_233])).
% 3.64/1.67  tff(c_247, plain, (![A_81]: (k1_relat_1(k5_relat_1(A_81, '#skF_2'))=k10_relat_1(A_81, '#skF_1') | ~v1_relat_1(A_81))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_242])).
% 3.64/1.67  tff(c_40, plain, (k1_relat_1(k5_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.64/1.67  tff(c_269, plain, (k10_relat_1('#skF_3', '#skF_1')!=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_247, c_40])).
% 3.64/1.67  tff(c_279, plain, (k10_relat_1('#skF_3', '#skF_1')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_269])).
% 3.64/1.67  tff(c_42, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.64/1.67  tff(c_44, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.64/1.67  tff(c_12, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.64/1.67  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.64/1.67  tff(c_296, plain, (![C_83, A_84, B_85]: (m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))) | ~r1_tarski(k2_relat_1(C_83), B_85) | ~r1_tarski(k1_relat_1(C_83), A_84) | ~v1_relat_1(C_83))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.64/1.67  tff(c_28, plain, (![C_25, A_23, B_24]: (v4_relat_1(C_25, A_23) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.64/1.67  tff(c_620, plain, (![C_115, A_116, B_117]: (v4_relat_1(C_115, A_116) | ~r1_tarski(k2_relat_1(C_115), B_117) | ~r1_tarski(k1_relat_1(C_115), A_116) | ~v1_relat_1(C_115))), inference(resolution, [status(thm)], [c_296, c_28])).
% 3.64/1.67  tff(c_641, plain, (![C_121, A_122]: (v4_relat_1(C_121, A_122) | ~r1_tarski(k1_relat_1(C_121), A_122) | ~v1_relat_1(C_121))), inference(resolution, [status(thm)], [c_6, c_620])).
% 3.64/1.67  tff(c_683, plain, (![C_124]: (v4_relat_1(C_124, k1_relat_1(C_124)) | ~v1_relat_1(C_124))), inference(resolution, [status(thm)], [c_6, c_641])).
% 3.64/1.67  tff(c_20, plain, (![B_16, A_15]: (k7_relat_1(B_16, A_15)=B_16 | ~v4_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.64/1.67  tff(c_730, plain, (![C_128]: (k7_relat_1(C_128, k1_relat_1(C_128))=C_128 | ~v1_relat_1(C_128))), inference(resolution, [status(thm)], [c_683, c_20])).
% 3.64/1.67  tff(c_16, plain, (![B_11, A_10]: (k2_relat_1(k7_relat_1(B_11, A_10))=k9_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.64/1.67  tff(c_736, plain, (![C_128]: (k9_relat_1(C_128, k1_relat_1(C_128))=k2_relat_1(C_128) | ~v1_relat_1(C_128) | ~v1_relat_1(C_128))), inference(superposition, [status(thm), theory('equality')], [c_730, c_16])).
% 3.64/1.67  tff(c_782, plain, (![A_131, C_132, B_133]: (r1_tarski(A_131, k10_relat_1(C_132, B_133)) | ~r1_tarski(k9_relat_1(C_132, A_131), B_133) | ~r1_tarski(A_131, k1_relat_1(C_132)) | ~v1_funct_1(C_132) | ~v1_relat_1(C_132))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.64/1.67  tff(c_785, plain, (![C_128, B_133]: (r1_tarski(k1_relat_1(C_128), k10_relat_1(C_128, B_133)) | ~r1_tarski(k2_relat_1(C_128), B_133) | ~r1_tarski(k1_relat_1(C_128), k1_relat_1(C_128)) | ~v1_funct_1(C_128) | ~v1_relat_1(C_128) | ~v1_relat_1(C_128) | ~v1_relat_1(C_128))), inference(superposition, [status(thm), theory('equality')], [c_736, c_782])).
% 3.64/1.67  tff(c_1545, plain, (![C_173, B_174]: (r1_tarski(k1_relat_1(C_173), k10_relat_1(C_173, B_174)) | ~r1_tarski(k2_relat_1(C_173), B_174) | ~v1_funct_1(C_173) | ~v1_relat_1(C_173))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_785])).
% 3.64/1.67  tff(c_22, plain, (![A_17, B_19]: (r1_tarski(k1_relat_1(k5_relat_1(A_17, B_19)), k1_relat_1(A_17)) | ~v1_relat_1(B_19) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.64/1.67  tff(c_260, plain, (![A_81]: (r1_tarski(k10_relat_1(A_81, '#skF_1'), k1_relat_1(A_81)) | ~v1_relat_1('#skF_2') | ~v1_relat_1(A_81) | ~v1_relat_1(A_81))), inference(superposition, [status(thm), theory('equality')], [c_247, c_22])).
% 3.64/1.67  tff(c_284, plain, (![A_82]: (r1_tarski(k10_relat_1(A_82, '#skF_1'), k1_relat_1(A_82)) | ~v1_relat_1(A_82))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_260])).
% 3.64/1.67  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.64/1.67  tff(c_293, plain, (![A_82]: (k10_relat_1(A_82, '#skF_1')=k1_relat_1(A_82) | ~r1_tarski(k1_relat_1(A_82), k10_relat_1(A_82, '#skF_1')) | ~v1_relat_1(A_82))), inference(resolution, [status(thm)], [c_284, c_2])).
% 3.64/1.67  tff(c_1582, plain, (![C_175]: (k10_relat_1(C_175, '#skF_1')=k1_relat_1(C_175) | ~r1_tarski(k2_relat_1(C_175), '#skF_1') | ~v1_funct_1(C_175) | ~v1_relat_1(C_175))), inference(resolution, [status(thm)], [c_1545, c_293])).
% 3.64/1.67  tff(c_1598, plain, (![B_176]: (k10_relat_1(B_176, '#skF_1')=k1_relat_1(B_176) | ~v1_funct_1(B_176) | ~v5_relat_1(B_176, '#skF_1') | ~v1_relat_1(B_176))), inference(resolution, [status(thm)], [c_12, c_1582])).
% 3.64/1.67  tff(c_1608, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_1598])).
% 3.64/1.67  tff(c_1615, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_1608])).
% 3.64/1.67  tff(c_1617, plain, $false, inference(negUnitSimplification, [status(thm)], [c_279, c_1615])).
% 3.64/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.64/1.67  
% 3.64/1.67  Inference rules
% 3.64/1.67  ----------------------
% 3.64/1.67  #Ref     : 0
% 3.64/1.67  #Sup     : 335
% 3.64/1.67  #Fact    : 0
% 3.64/1.67  #Define  : 0
% 3.64/1.67  #Split   : 4
% 3.64/1.67  #Chain   : 0
% 3.64/1.67  #Close   : 0
% 3.64/1.67  
% 3.64/1.67  Ordering : KBO
% 3.64/1.67  
% 3.64/1.67  Simplification rules
% 3.64/1.67  ----------------------
% 3.64/1.67  #Subsume      : 38
% 3.64/1.67  #Demod        : 336
% 3.64/1.67  #Tautology    : 127
% 3.64/1.67  #SimpNegUnit  : 4
% 3.64/1.67  #BackRed      : 1
% 3.64/1.67  
% 3.64/1.67  #Partial instantiations: 0
% 3.64/1.67  #Strategies tried      : 1
% 3.64/1.67  
% 3.64/1.67  Timing (in seconds)
% 3.64/1.67  ----------------------
% 3.64/1.68  Preprocessing        : 0.33
% 3.64/1.68  Parsing              : 0.17
% 3.64/1.68  CNF conversion       : 0.02
% 3.64/1.68  Main loop            : 0.49
% 3.64/1.68  Inferencing          : 0.18
% 3.64/1.68  Reduction            : 0.16
% 3.64/1.68  Demodulation         : 0.12
% 3.64/1.68  BG Simplification    : 0.02
% 3.64/1.68  Subsumption          : 0.08
% 3.64/1.68  Abstraction          : 0.03
% 3.64/1.68  MUC search           : 0.00
% 3.64/1.68  Cooper               : 0.00
% 3.64/1.68  Total                : 0.85
% 3.64/1.68  Index Insertion      : 0.00
% 3.64/1.68  Index Deletion       : 0.00
% 3.64/1.68  Index Matching       : 0.00
% 3.64/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
