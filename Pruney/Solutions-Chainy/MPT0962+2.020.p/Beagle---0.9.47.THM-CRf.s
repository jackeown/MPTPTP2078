%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:54 EST 2020

% Result     : Theorem 4.50s
% Output     : CNFRefutation 4.57s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 527 expanded)
%              Number of leaves         :   36 ( 180 expanded)
%              Depth                    :   11
%              Number of atoms          :  229 (1261 expanded)
%              Number of equality atoms :   67 ( 343 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_117,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r1_tarski(k2_relat_1(B),A)
         => ( v1_funct_1(B)
            & v1_funct_2(B,k1_relat_1(B),A)
            & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_43,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_104,axiom,(
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

tff(f_47,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_45,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_57,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(c_56,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_14,plain,(
    ! [B_9] : r1_tarski(B_9,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_52,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_2759,plain,(
    ! [C_379,A_380,B_381] :
      ( m1_subset_1(C_379,k1_zfmisc_1(k2_zfmisc_1(A_380,B_381)))
      | ~ r1_tarski(k2_relat_1(C_379),B_381)
      | ~ r1_tarski(k1_relat_1(C_379),A_380)
      | ~ v1_relat_1(C_379) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_54,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_50,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_58,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50])).

tff(c_78,plain,(
    ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_26,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(A_16,k1_zfmisc_1(B_17))
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_273,plain,(
    ! [C_58,B_59,A_60] :
      ( ~ v1_xboole_0(C_58)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(C_58))
      | ~ r2_hidden(A_60,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_277,plain,(
    ! [B_61,A_62,A_63] :
      ( ~ v1_xboole_0(B_61)
      | ~ r2_hidden(A_62,A_63)
      | ~ r1_tarski(A_63,B_61) ) ),
    inference(resolution,[status(thm)],[c_26,c_273])).

tff(c_281,plain,(
    ! [B_64,A_65] :
      ( ~ v1_xboole_0(B_64)
      | ~ r1_tarski(A_65,B_64)
      | v1_xboole_0(A_65) ) ),
    inference(resolution,[status(thm)],[c_6,c_277])).

tff(c_301,plain,
    ( ~ v1_xboole_0('#skF_2')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_52,c_281])).

tff(c_303,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_301])).

tff(c_490,plain,(
    ! [C_103,A_104,B_105] :
      ( m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105)))
      | ~ r1_tarski(k2_relat_1(C_103),B_105)
      | ~ r1_tarski(k1_relat_1(C_103),A_104)
      | ~ v1_relat_1(C_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_24,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(A_16,B_17)
      | ~ m1_subset_1(A_16,k1_zfmisc_1(B_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_552,plain,(
    ! [C_112,A_113,B_114] :
      ( r1_tarski(C_112,k2_zfmisc_1(A_113,B_114))
      | ~ r1_tarski(k2_relat_1(C_112),B_114)
      | ~ r1_tarski(k1_relat_1(C_112),A_113)
      | ~ v1_relat_1(C_112) ) ),
    inference(resolution,[status(thm)],[c_490,c_24])).

tff(c_560,plain,(
    ! [A_113] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(A_113,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_113)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_52,c_552])).

tff(c_570,plain,(
    ! [A_115] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(A_115,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_560])).

tff(c_585,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_14,c_570])).

tff(c_348,plain,(
    ! [A_72,B_73,C_74] :
      ( k1_relset_1(A_72,B_73,C_74) = k1_relat_1(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_353,plain,(
    ! [A_72,B_73,A_16] :
      ( k1_relset_1(A_72,B_73,A_16) = k1_relat_1(A_16)
      | ~ r1_tarski(A_16,k2_zfmisc_1(A_72,B_73)) ) ),
    inference(resolution,[status(thm)],[c_26,c_348])).

tff(c_594,plain,(
    k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_585,c_353])).

tff(c_542,plain,(
    ! [B_109,C_110,A_111] :
      ( k1_xboole_0 = B_109
      | v1_funct_2(C_110,A_111,B_109)
      | k1_relset_1(A_111,B_109,C_110) != A_111
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_111,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_815,plain,(
    ! [B_132,A_133,A_134] :
      ( k1_xboole_0 = B_132
      | v1_funct_2(A_133,A_134,B_132)
      | k1_relset_1(A_134,B_132,A_133) != A_134
      | ~ r1_tarski(A_133,k2_zfmisc_1(A_134,B_132)) ) ),
    inference(resolution,[status(thm)],[c_26,c_542])).

tff(c_827,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2')
    | k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') != k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_585,c_815])).

tff(c_843,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_594,c_827])).

tff(c_844,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_843])).

tff(c_18,plain,(
    ! [A_11] : r1_xboole_0(A_11,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_244,plain,(
    ! [B_54,A_55] :
      ( ~ r1_xboole_0(B_54,A_55)
      | ~ r1_tarski(B_54,A_55)
      | v1_xboole_0(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_249,plain,(
    ! [A_56] :
      ( ~ r1_tarski(A_56,k1_xboole_0)
      | v1_xboole_0(A_56) ) ),
    inference(resolution,[status(thm)],[c_18,c_244])).

tff(c_259,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_249])).

tff(c_869,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_844,c_259])).

tff(c_880,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_303,c_869])).

tff(c_882,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_301])).

tff(c_8,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_886,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_882,c_8])).

tff(c_79,plain,(
    ! [B_39,A_40] : k2_xboole_0(B_39,A_40) = k2_xboole_0(A_40,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_10] : k2_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_132,plain,(
    ! [A_41] : k2_xboole_0(k1_xboole_0,A_41) = A_41 ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_16])).

tff(c_22,plain,(
    ! [A_14,B_15] : r1_tarski(A_14,k2_xboole_0(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_144,plain,(
    ! [A_41] : r1_tarski(k1_xboole_0,A_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_22])).

tff(c_894,plain,(
    ! [A_41] : r1_tarski('#skF_2',A_41) ),
    inference(demodulation,[status(thm),theory(equality)],[c_886,c_144])).

tff(c_205,plain,(
    ! [B_50,A_51] :
      ( B_50 = A_51
      | ~ r1_tarski(B_50,A_51)
      | ~ r1_tarski(A_51,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_219,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_52,c_205])).

tff(c_237,plain,(
    ~ r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_219])).

tff(c_911,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_894,c_237])).

tff(c_912,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_219])).

tff(c_921,plain,(
    ! [A_136] :
      ( k2_relat_1(A_136) = k1_xboole_0
      | k1_relat_1(A_136) != k1_xboole_0
      | ~ v1_relat_1(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_924,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_921])).

tff(c_926,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_912,c_924])).

tff(c_949,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_926])).

tff(c_950,plain,(
    ! [A_140] :
      ( k1_relat_1(A_140) = k1_xboole_0
      | k2_relat_1(A_140) != k1_xboole_0
      | ~ v1_relat_1(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_953,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_950])).

tff(c_955,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | k1_xboole_0 != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_912,c_953])).

tff(c_956,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_949,c_955])).

tff(c_1161,plain,(
    ! [C_184,A_185,B_186] :
      ( m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(A_185,B_186)))
      | ~ r1_tarski(k2_relat_1(C_184),B_186)
      | ~ r1_tarski(k1_relat_1(C_184),A_185)
      | ~ v1_relat_1(C_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1231,plain,(
    ! [C_195,A_196,B_197] :
      ( r1_tarski(C_195,k2_zfmisc_1(A_196,B_197))
      | ~ r1_tarski(k2_relat_1(C_195),B_197)
      | ~ r1_tarski(k1_relat_1(C_195),A_196)
      | ~ v1_relat_1(C_195) ) ),
    inference(resolution,[status(thm)],[c_1161,c_24])).

tff(c_1248,plain,(
    ! [C_198,A_199] :
      ( r1_tarski(C_198,k2_zfmisc_1(A_199,k2_relat_1(C_198)))
      | ~ r1_tarski(k1_relat_1(C_198),A_199)
      | ~ v1_relat_1(C_198) ) ),
    inference(resolution,[status(thm)],[c_14,c_1231])).

tff(c_1270,plain,(
    ! [A_199] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(A_199,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_199)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_912,c_1248])).

tff(c_1279,plain,(
    ! [A_200] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(A_200,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_200) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1270])).

tff(c_1299,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_14,c_1279])).

tff(c_1005,plain,(
    ! [A_153,B_154,C_155] :
      ( k1_relset_1(A_153,B_154,C_155) = k1_relat_1(C_155)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(A_153,B_154))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1010,plain,(
    ! [A_153,B_154,A_16] :
      ( k1_relset_1(A_153,B_154,A_16) = k1_relat_1(A_16)
      | ~ r1_tarski(A_16,k2_zfmisc_1(A_153,B_154)) ) ),
    inference(resolution,[status(thm)],[c_26,c_1005])).

tff(c_1325,plain,(
    k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1299,c_1010])).

tff(c_1358,plain,(
    ! [B_204,C_205,A_206] :
      ( k1_xboole_0 = B_204
      | v1_funct_2(C_205,A_206,B_204)
      | k1_relset_1(A_206,B_204,C_205) != A_206
      | ~ m1_subset_1(C_205,k1_zfmisc_1(k2_zfmisc_1(A_206,B_204))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1693,plain,(
    ! [B_230,A_231,A_232] :
      ( k1_xboole_0 = B_230
      | v1_funct_2(A_231,A_232,B_230)
      | k1_relset_1(A_232,B_230,A_231) != A_232
      | ~ r1_tarski(A_231,k2_zfmisc_1(A_232,B_230)) ) ),
    inference(resolution,[status(thm)],[c_26,c_1358])).

tff(c_1711,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2')
    | k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') != k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1299,c_1693])).

tff(c_1734,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1325,c_1711])).

tff(c_1736,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_956,c_1734])).

tff(c_1737,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_926])).

tff(c_1738,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_926])).

tff(c_1757,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1737,c_1738])).

tff(c_1743,plain,(
    ! [A_41] : r1_tarski('#skF_2',A_41) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1737,c_144])).

tff(c_2088,plain,(
    ! [C_283,A_284,B_285] :
      ( m1_subset_1(C_283,k1_zfmisc_1(k2_zfmisc_1(A_284,B_285)))
      | ~ r1_tarski(k2_relat_1(C_283),B_285)
      | ~ r1_tarski(k1_relat_1(C_283),A_284)
      | ~ v1_relat_1(C_283) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2173,plain,(
    ! [C_296,A_297,B_298] :
      ( r1_tarski(C_296,k2_zfmisc_1(A_297,B_298))
      | ~ r1_tarski(k2_relat_1(C_296),B_298)
      | ~ r1_tarski(k1_relat_1(C_296),A_297)
      | ~ v1_relat_1(C_296) ) ),
    inference(resolution,[status(thm)],[c_2088,c_24])).

tff(c_2175,plain,(
    ! [A_297,B_298] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(A_297,B_298))
      | ~ r1_tarski('#skF_2',B_298)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_297)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_912,c_2173])).

tff(c_2190,plain,(
    ! [A_299,B_300] : r1_tarski('#skF_3',k2_zfmisc_1(A_299,B_300)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1743,c_1757,c_1743,c_2175])).

tff(c_1891,plain,(
    ! [A_244,B_245,C_246] :
      ( k1_relset_1(A_244,B_245,C_246) = k1_relat_1(C_246)
      | ~ m1_subset_1(C_246,k1_zfmisc_1(k2_zfmisc_1(A_244,B_245))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1896,plain,(
    ! [A_244,B_245,A_16] :
      ( k1_relset_1(A_244,B_245,A_16) = k1_relat_1(A_16)
      | ~ r1_tarski(A_16,k2_zfmisc_1(A_244,B_245)) ) ),
    inference(resolution,[status(thm)],[c_26,c_1891])).

tff(c_2205,plain,(
    ! [A_299,B_300] : k1_relset_1(A_299,B_300,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2190,c_1896])).

tff(c_2215,plain,(
    ! [A_299,B_300] : k1_relset_1(A_299,B_300,'#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1757,c_2205])).

tff(c_42,plain,(
    ! [C_30,B_29] :
      ( v1_funct_2(C_30,k1_xboole_0,B_29)
      | k1_relset_1(k1_xboole_0,B_29,C_30) != k1_xboole_0
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2060,plain,(
    ! [C_276,B_277] :
      ( v1_funct_2(C_276,'#skF_2',B_277)
      | k1_relset_1('#skF_2',B_277,C_276) != '#skF_2'
      | ~ m1_subset_1(C_276,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_277))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1737,c_1737,c_1737,c_1737,c_42])).

tff(c_2065,plain,(
    ! [A_16,B_277] :
      ( v1_funct_2(A_16,'#skF_2',B_277)
      | k1_relset_1('#skF_2',B_277,A_16) != '#skF_2'
      | ~ r1_tarski(A_16,k2_zfmisc_1('#skF_2',B_277)) ) ),
    inference(resolution,[status(thm)],[c_26,c_2060])).

tff(c_2212,plain,(
    ! [B_300] :
      ( v1_funct_2('#skF_3','#skF_2',B_300)
      | k1_relset_1('#skF_2',B_300,'#skF_3') != '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_2190,c_2065])).

tff(c_2325,plain,(
    ! [B_300] : v1_funct_2('#skF_3','#skF_2',B_300) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2215,c_2212])).

tff(c_1758,plain,(
    ~ v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1757,c_78])).

tff(c_2328,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2325,c_1758])).

tff(c_2329,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_2782,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2759,c_2329])).

tff(c_2792,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_14,c_52,c_2782])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:31:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.50/1.82  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.57/1.84  
% 4.57/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.57/1.84  %$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 4.57/1.84  
% 4.57/1.84  %Foreground sorts:
% 4.57/1.84  
% 4.57/1.84  
% 4.57/1.84  %Background operators:
% 4.57/1.84  
% 4.57/1.84  
% 4.57/1.84  %Foreground operators:
% 4.57/1.84  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.57/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.57/1.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.57/1.84  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.57/1.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.57/1.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.57/1.84  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.57/1.84  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.57/1.84  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.57/1.84  tff('#skF_2', type, '#skF_2': $i).
% 4.57/1.84  tff('#skF_3', type, '#skF_3': $i).
% 4.57/1.84  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.57/1.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.57/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.57/1.84  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.57/1.84  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.57/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.57/1.84  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.57/1.84  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.57/1.84  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.57/1.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.57/1.84  
% 4.57/1.86  tff(f_117, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 4.57/1.86  tff(f_43, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.57/1.86  tff(f_86, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 4.57/1.86  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.57/1.86  tff(f_61, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.57/1.86  tff(f_68, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 4.57/1.86  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.57/1.86  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.57/1.86  tff(f_47, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.57/1.86  tff(f_55, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 4.57/1.86  tff(f_37, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.57/1.86  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.57/1.86  tff(f_45, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 4.57/1.86  tff(f_57, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.57/1.86  tff(f_74, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 4.57/1.86  tff(c_56, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.57/1.86  tff(c_14, plain, (![B_9]: (r1_tarski(B_9, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.57/1.86  tff(c_52, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.57/1.86  tff(c_2759, plain, (![C_379, A_380, B_381]: (m1_subset_1(C_379, k1_zfmisc_1(k2_zfmisc_1(A_380, B_381))) | ~r1_tarski(k2_relat_1(C_379), B_381) | ~r1_tarski(k1_relat_1(C_379), A_380) | ~v1_relat_1(C_379))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.57/1.86  tff(c_54, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.57/1.86  tff(c_50, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2') | ~v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.57/1.86  tff(c_58, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50])).
% 4.57/1.86  tff(c_78, plain, (~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_58])).
% 4.57/1.86  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.57/1.86  tff(c_26, plain, (![A_16, B_17]: (m1_subset_1(A_16, k1_zfmisc_1(B_17)) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.57/1.86  tff(c_273, plain, (![C_58, B_59, A_60]: (~v1_xboole_0(C_58) | ~m1_subset_1(B_59, k1_zfmisc_1(C_58)) | ~r2_hidden(A_60, B_59))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.57/1.86  tff(c_277, plain, (![B_61, A_62, A_63]: (~v1_xboole_0(B_61) | ~r2_hidden(A_62, A_63) | ~r1_tarski(A_63, B_61))), inference(resolution, [status(thm)], [c_26, c_273])).
% 4.57/1.86  tff(c_281, plain, (![B_64, A_65]: (~v1_xboole_0(B_64) | ~r1_tarski(A_65, B_64) | v1_xboole_0(A_65))), inference(resolution, [status(thm)], [c_6, c_277])).
% 4.57/1.86  tff(c_301, plain, (~v1_xboole_0('#skF_2') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_52, c_281])).
% 4.57/1.86  tff(c_303, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_301])).
% 4.57/1.86  tff(c_490, plain, (![C_103, A_104, B_105]: (m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))) | ~r1_tarski(k2_relat_1(C_103), B_105) | ~r1_tarski(k1_relat_1(C_103), A_104) | ~v1_relat_1(C_103))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.57/1.86  tff(c_24, plain, (![A_16, B_17]: (r1_tarski(A_16, B_17) | ~m1_subset_1(A_16, k1_zfmisc_1(B_17)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.57/1.86  tff(c_552, plain, (![C_112, A_113, B_114]: (r1_tarski(C_112, k2_zfmisc_1(A_113, B_114)) | ~r1_tarski(k2_relat_1(C_112), B_114) | ~r1_tarski(k1_relat_1(C_112), A_113) | ~v1_relat_1(C_112))), inference(resolution, [status(thm)], [c_490, c_24])).
% 4.57/1.86  tff(c_560, plain, (![A_113]: (r1_tarski('#skF_3', k2_zfmisc_1(A_113, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), A_113) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_52, c_552])).
% 4.57/1.86  tff(c_570, plain, (![A_115]: (r1_tarski('#skF_3', k2_zfmisc_1(A_115, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), A_115))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_560])).
% 4.57/1.86  tff(c_585, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))), inference(resolution, [status(thm)], [c_14, c_570])).
% 4.57/1.86  tff(c_348, plain, (![A_72, B_73, C_74]: (k1_relset_1(A_72, B_73, C_74)=k1_relat_1(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.57/1.86  tff(c_353, plain, (![A_72, B_73, A_16]: (k1_relset_1(A_72, B_73, A_16)=k1_relat_1(A_16) | ~r1_tarski(A_16, k2_zfmisc_1(A_72, B_73)))), inference(resolution, [status(thm)], [c_26, c_348])).
% 4.57/1.86  tff(c_594, plain, (k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_585, c_353])).
% 4.57/1.86  tff(c_542, plain, (![B_109, C_110, A_111]: (k1_xboole_0=B_109 | v1_funct_2(C_110, A_111, B_109) | k1_relset_1(A_111, B_109, C_110)!=A_111 | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_111, B_109))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.57/1.86  tff(c_815, plain, (![B_132, A_133, A_134]: (k1_xboole_0=B_132 | v1_funct_2(A_133, A_134, B_132) | k1_relset_1(A_134, B_132, A_133)!=A_134 | ~r1_tarski(A_133, k2_zfmisc_1(A_134, B_132)))), inference(resolution, [status(thm)], [c_26, c_542])).
% 4.57/1.86  tff(c_827, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2') | k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')!=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_585, c_815])).
% 4.57/1.86  tff(c_843, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_594, c_827])).
% 4.57/1.86  tff(c_844, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_78, c_843])).
% 4.57/1.86  tff(c_18, plain, (![A_11]: (r1_xboole_0(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.57/1.86  tff(c_244, plain, (![B_54, A_55]: (~r1_xboole_0(B_54, A_55) | ~r1_tarski(B_54, A_55) | v1_xboole_0(B_54))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.57/1.86  tff(c_249, plain, (![A_56]: (~r1_tarski(A_56, k1_xboole_0) | v1_xboole_0(A_56))), inference(resolution, [status(thm)], [c_18, c_244])).
% 4.57/1.86  tff(c_259, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_249])).
% 4.57/1.86  tff(c_869, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_844, c_259])).
% 4.57/1.86  tff(c_880, plain, $false, inference(negUnitSimplification, [status(thm)], [c_303, c_869])).
% 4.57/1.86  tff(c_882, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_301])).
% 4.57/1.86  tff(c_8, plain, (![A_7]: (k1_xboole_0=A_7 | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.57/1.86  tff(c_886, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_882, c_8])).
% 4.57/1.86  tff(c_79, plain, (![B_39, A_40]: (k2_xboole_0(B_39, A_40)=k2_xboole_0(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.57/1.86  tff(c_16, plain, (![A_10]: (k2_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.57/1.86  tff(c_132, plain, (![A_41]: (k2_xboole_0(k1_xboole_0, A_41)=A_41)), inference(superposition, [status(thm), theory('equality')], [c_79, c_16])).
% 4.57/1.86  tff(c_22, plain, (![A_14, B_15]: (r1_tarski(A_14, k2_xboole_0(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.57/1.86  tff(c_144, plain, (![A_41]: (r1_tarski(k1_xboole_0, A_41))), inference(superposition, [status(thm), theory('equality')], [c_132, c_22])).
% 4.57/1.86  tff(c_894, plain, (![A_41]: (r1_tarski('#skF_2', A_41))), inference(demodulation, [status(thm), theory('equality')], [c_886, c_144])).
% 4.57/1.86  tff(c_205, plain, (![B_50, A_51]: (B_50=A_51 | ~r1_tarski(B_50, A_51) | ~r1_tarski(A_51, B_50))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.57/1.86  tff(c_219, plain, (k2_relat_1('#skF_3')='#skF_2' | ~r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_52, c_205])).
% 4.57/1.86  tff(c_237, plain, (~r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_219])).
% 4.57/1.86  tff(c_911, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_894, c_237])).
% 4.57/1.86  tff(c_912, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_219])).
% 4.57/1.86  tff(c_921, plain, (![A_136]: (k2_relat_1(A_136)=k1_xboole_0 | k1_relat_1(A_136)!=k1_xboole_0 | ~v1_relat_1(A_136))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.57/1.86  tff(c_924, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k1_relat_1('#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_56, c_921])).
% 4.57/1.86  tff(c_926, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_912, c_924])).
% 4.57/1.86  tff(c_949, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_926])).
% 4.57/1.86  tff(c_950, plain, (![A_140]: (k1_relat_1(A_140)=k1_xboole_0 | k2_relat_1(A_140)!=k1_xboole_0 | ~v1_relat_1(A_140))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.57/1.86  tff(c_953, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | k2_relat_1('#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_56, c_950])).
% 4.57/1.86  tff(c_955, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | k1_xboole_0!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_912, c_953])).
% 4.57/1.86  tff(c_956, plain, (k1_xboole_0!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_949, c_955])).
% 4.57/1.86  tff(c_1161, plain, (![C_184, A_185, B_186]: (m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(A_185, B_186))) | ~r1_tarski(k2_relat_1(C_184), B_186) | ~r1_tarski(k1_relat_1(C_184), A_185) | ~v1_relat_1(C_184))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.57/1.86  tff(c_1231, plain, (![C_195, A_196, B_197]: (r1_tarski(C_195, k2_zfmisc_1(A_196, B_197)) | ~r1_tarski(k2_relat_1(C_195), B_197) | ~r1_tarski(k1_relat_1(C_195), A_196) | ~v1_relat_1(C_195))), inference(resolution, [status(thm)], [c_1161, c_24])).
% 4.57/1.86  tff(c_1248, plain, (![C_198, A_199]: (r1_tarski(C_198, k2_zfmisc_1(A_199, k2_relat_1(C_198))) | ~r1_tarski(k1_relat_1(C_198), A_199) | ~v1_relat_1(C_198))), inference(resolution, [status(thm)], [c_14, c_1231])).
% 4.57/1.86  tff(c_1270, plain, (![A_199]: (r1_tarski('#skF_3', k2_zfmisc_1(A_199, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), A_199) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_912, c_1248])).
% 4.57/1.86  tff(c_1279, plain, (![A_200]: (r1_tarski('#skF_3', k2_zfmisc_1(A_200, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), A_200))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1270])).
% 4.57/1.86  tff(c_1299, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))), inference(resolution, [status(thm)], [c_14, c_1279])).
% 4.57/1.86  tff(c_1005, plain, (![A_153, B_154, C_155]: (k1_relset_1(A_153, B_154, C_155)=k1_relat_1(C_155) | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(A_153, B_154))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.57/1.86  tff(c_1010, plain, (![A_153, B_154, A_16]: (k1_relset_1(A_153, B_154, A_16)=k1_relat_1(A_16) | ~r1_tarski(A_16, k2_zfmisc_1(A_153, B_154)))), inference(resolution, [status(thm)], [c_26, c_1005])).
% 4.57/1.86  tff(c_1325, plain, (k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1299, c_1010])).
% 4.57/1.86  tff(c_1358, plain, (![B_204, C_205, A_206]: (k1_xboole_0=B_204 | v1_funct_2(C_205, A_206, B_204) | k1_relset_1(A_206, B_204, C_205)!=A_206 | ~m1_subset_1(C_205, k1_zfmisc_1(k2_zfmisc_1(A_206, B_204))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.57/1.86  tff(c_1693, plain, (![B_230, A_231, A_232]: (k1_xboole_0=B_230 | v1_funct_2(A_231, A_232, B_230) | k1_relset_1(A_232, B_230, A_231)!=A_232 | ~r1_tarski(A_231, k2_zfmisc_1(A_232, B_230)))), inference(resolution, [status(thm)], [c_26, c_1358])).
% 4.57/1.86  tff(c_1711, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2') | k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')!=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1299, c_1693])).
% 4.57/1.86  tff(c_1734, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1325, c_1711])).
% 4.57/1.86  tff(c_1736, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_956, c_1734])).
% 4.57/1.86  tff(c_1737, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_926])).
% 4.57/1.86  tff(c_1738, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_926])).
% 4.57/1.86  tff(c_1757, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1737, c_1738])).
% 4.57/1.86  tff(c_1743, plain, (![A_41]: (r1_tarski('#skF_2', A_41))), inference(demodulation, [status(thm), theory('equality')], [c_1737, c_144])).
% 4.57/1.86  tff(c_2088, plain, (![C_283, A_284, B_285]: (m1_subset_1(C_283, k1_zfmisc_1(k2_zfmisc_1(A_284, B_285))) | ~r1_tarski(k2_relat_1(C_283), B_285) | ~r1_tarski(k1_relat_1(C_283), A_284) | ~v1_relat_1(C_283))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.57/1.86  tff(c_2173, plain, (![C_296, A_297, B_298]: (r1_tarski(C_296, k2_zfmisc_1(A_297, B_298)) | ~r1_tarski(k2_relat_1(C_296), B_298) | ~r1_tarski(k1_relat_1(C_296), A_297) | ~v1_relat_1(C_296))), inference(resolution, [status(thm)], [c_2088, c_24])).
% 4.57/1.86  tff(c_2175, plain, (![A_297, B_298]: (r1_tarski('#skF_3', k2_zfmisc_1(A_297, B_298)) | ~r1_tarski('#skF_2', B_298) | ~r1_tarski(k1_relat_1('#skF_3'), A_297) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_912, c_2173])).
% 4.57/1.86  tff(c_2190, plain, (![A_299, B_300]: (r1_tarski('#skF_3', k2_zfmisc_1(A_299, B_300)))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1743, c_1757, c_1743, c_2175])).
% 4.57/1.86  tff(c_1891, plain, (![A_244, B_245, C_246]: (k1_relset_1(A_244, B_245, C_246)=k1_relat_1(C_246) | ~m1_subset_1(C_246, k1_zfmisc_1(k2_zfmisc_1(A_244, B_245))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.57/1.86  tff(c_1896, plain, (![A_244, B_245, A_16]: (k1_relset_1(A_244, B_245, A_16)=k1_relat_1(A_16) | ~r1_tarski(A_16, k2_zfmisc_1(A_244, B_245)))), inference(resolution, [status(thm)], [c_26, c_1891])).
% 4.57/1.86  tff(c_2205, plain, (![A_299, B_300]: (k1_relset_1(A_299, B_300, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_2190, c_1896])).
% 4.57/1.86  tff(c_2215, plain, (![A_299, B_300]: (k1_relset_1(A_299, B_300, '#skF_3')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1757, c_2205])).
% 4.57/1.86  tff(c_42, plain, (![C_30, B_29]: (v1_funct_2(C_30, k1_xboole_0, B_29) | k1_relset_1(k1_xboole_0, B_29, C_30)!=k1_xboole_0 | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_29))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.57/1.86  tff(c_2060, plain, (![C_276, B_277]: (v1_funct_2(C_276, '#skF_2', B_277) | k1_relset_1('#skF_2', B_277, C_276)!='#skF_2' | ~m1_subset_1(C_276, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_277))))), inference(demodulation, [status(thm), theory('equality')], [c_1737, c_1737, c_1737, c_1737, c_42])).
% 4.57/1.86  tff(c_2065, plain, (![A_16, B_277]: (v1_funct_2(A_16, '#skF_2', B_277) | k1_relset_1('#skF_2', B_277, A_16)!='#skF_2' | ~r1_tarski(A_16, k2_zfmisc_1('#skF_2', B_277)))), inference(resolution, [status(thm)], [c_26, c_2060])).
% 4.57/1.86  tff(c_2212, plain, (![B_300]: (v1_funct_2('#skF_3', '#skF_2', B_300) | k1_relset_1('#skF_2', B_300, '#skF_3')!='#skF_2')), inference(resolution, [status(thm)], [c_2190, c_2065])).
% 4.57/1.86  tff(c_2325, plain, (![B_300]: (v1_funct_2('#skF_3', '#skF_2', B_300))), inference(demodulation, [status(thm), theory('equality')], [c_2215, c_2212])).
% 4.57/1.86  tff(c_1758, plain, (~v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1757, c_78])).
% 4.57/1.86  tff(c_2328, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2325, c_1758])).
% 4.57/1.86  tff(c_2329, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')))), inference(splitRight, [status(thm)], [c_58])).
% 4.57/1.86  tff(c_2782, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2759, c_2329])).
% 4.57/1.86  tff(c_2792, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_14, c_52, c_2782])).
% 4.57/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.57/1.86  
% 4.57/1.86  Inference rules
% 4.57/1.86  ----------------------
% 4.57/1.86  #Ref     : 0
% 4.57/1.86  #Sup     : 565
% 4.57/1.86  #Fact    : 0
% 4.57/1.86  #Define  : 0
% 4.57/1.86  #Split   : 22
% 4.57/1.86  #Chain   : 0
% 4.57/1.86  #Close   : 0
% 4.57/1.86  
% 4.57/1.86  Ordering : KBO
% 4.57/1.86  
% 4.57/1.86  Simplification rules
% 4.57/1.86  ----------------------
% 4.57/1.86  #Subsume      : 85
% 4.57/1.86  #Demod        : 389
% 4.57/1.86  #Tautology    : 236
% 4.57/1.86  #SimpNegUnit  : 16
% 4.57/1.86  #BackRed      : 85
% 4.57/1.86  
% 4.57/1.86  #Partial instantiations: 0
% 4.57/1.86  #Strategies tried      : 1
% 4.57/1.86  
% 4.57/1.86  Timing (in seconds)
% 4.57/1.86  ----------------------
% 4.57/1.86  Preprocessing        : 0.34
% 4.57/1.86  Parsing              : 0.19
% 4.57/1.86  CNF conversion       : 0.02
% 4.57/1.86  Main loop            : 0.71
% 4.57/1.86  Inferencing          : 0.25
% 4.57/1.86  Reduction            : 0.23
% 4.57/1.86  Demodulation         : 0.16
% 4.57/1.86  BG Simplification    : 0.03
% 4.57/1.86  Subsumption          : 0.13
% 4.57/1.86  Abstraction          : 0.03
% 4.57/1.86  MUC search           : 0.00
% 4.57/1.86  Cooper               : 0.00
% 4.57/1.86  Total                : 1.09
% 4.57/1.86  Index Insertion      : 0.00
% 4.57/1.86  Index Deletion       : 0.00
% 4.57/1.86  Index Matching       : 0.00
% 4.57/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
