%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:11 EST 2020

% Result     : Theorem 3.43s
% Output     : CNFRefutation 3.43s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 125 expanded)
%              Number of leaves         :   44 (  62 expanded)
%              Depth                    :   11
%              Number of atoms          :  133 ( 233 expanded)
%              Number of equality atoms :   46 (  85 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_124,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_113,axiom,(
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

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_50,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_52,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_48,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_79,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_66,plain,(
    k1_funct_1('#skF_7','#skF_6') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_68,plain,(
    r2_hidden('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_72,plain,(
    v1_funct_2('#skF_7','#skF_4',k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_70,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_tarski('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_261,plain,(
    ! [A_104,B_105,C_106] :
      ( k1_relset_1(A_104,B_105,C_106) = k1_relat_1(C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_265,plain,(
    k1_relset_1('#skF_4',k1_tarski('#skF_5'),'#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_70,c_261])).

tff(c_1051,plain,(
    ! [B_232,A_233,C_234] :
      ( k1_xboole_0 = B_232
      | k1_relset_1(A_233,B_232,C_234) = A_233
      | ~ v1_funct_2(C_234,A_233,B_232)
      | ~ m1_subset_1(C_234,k1_zfmisc_1(k2_zfmisc_1(A_233,B_232))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1058,plain,
    ( k1_tarski('#skF_5') = k1_xboole_0
    | k1_relset_1('#skF_4',k1_tarski('#skF_5'),'#skF_7') = '#skF_4'
    | ~ v1_funct_2('#skF_7','#skF_4',k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_70,c_1051])).

tff(c_1062,plain,
    ( k1_tarski('#skF_5') = k1_xboole_0
    | k1_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_265,c_1058])).

tff(c_1069,plain,(
    k1_relat_1('#skF_7') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1062])).

tff(c_215,plain,(
    ! [C_81,A_82,B_83] :
      ( v1_relat_1(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_219,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_70,c_215])).

tff(c_74,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_727,plain,(
    ! [B_169,A_170] :
      ( r2_hidden(k1_funct_1(B_169,A_170),k2_relat_1(B_169))
      | ~ r2_hidden(A_170,k1_relat_1(B_169))
      | ~ v1_funct_1(B_169)
      | ~ v1_relat_1(B_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_252,plain,(
    ! [A_101,B_102,C_103] :
      ( k2_relset_1(A_101,B_102,C_103) = k2_relat_1(C_103)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_256,plain,(
    k2_relset_1('#skF_4',k1_tarski('#skF_5'),'#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_70,c_252])).

tff(c_356,plain,(
    ! [A_122,B_123,C_124] :
      ( m1_subset_1(k2_relset_1(A_122,B_123,C_124),k1_zfmisc_1(B_123))
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_373,plain,
    ( m1_subset_1(k2_relat_1('#skF_7'),k1_zfmisc_1(k1_tarski('#skF_5')))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_tarski('#skF_5')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_356])).

tff(c_379,plain,(
    m1_subset_1(k2_relat_1('#skF_7'),k1_zfmisc_1(k1_tarski('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_373])).

tff(c_40,plain,(
    ! [A_21,C_23,B_22] :
      ( m1_subset_1(A_21,C_23)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(C_23))
      | ~ r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_400,plain,(
    ! [A_21] :
      ( m1_subset_1(A_21,k1_tarski('#skF_5'))
      | ~ r2_hidden(A_21,k2_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_379,c_40])).

tff(c_731,plain,(
    ! [A_170] :
      ( m1_subset_1(k1_funct_1('#skF_7',A_170),k1_tarski('#skF_5'))
      | ~ r2_hidden(A_170,k1_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_727,c_400])).

tff(c_827,plain,(
    ! [A_174] :
      ( m1_subset_1(k1_funct_1('#skF_7',A_174),k1_tarski('#skF_5'))
      | ~ r2_hidden(A_174,k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_74,c_731])).

tff(c_32,plain,(
    ! [A_13] : k2_tarski(A_13,A_13) = k1_tarski(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_139,plain,(
    ! [A_66,B_67] : k1_enumset1(A_66,A_66,B_67) = k2_tarski(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_90,plain,(
    ! [E_47,A_48,C_49] : r2_hidden(E_47,k1_enumset1(A_48,E_47,C_49)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_94,plain,(
    ! [A_48,E_47,C_49] : ~ v1_xboole_0(k1_enumset1(A_48,E_47,C_49)) ),
    inference(resolution,[status(thm)],[c_90,c_2])).

tff(c_153,plain,(
    ! [A_66,B_67] : ~ v1_xboole_0(k2_tarski(A_66,B_67)) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_94])).

tff(c_38,plain,(
    ! [A_19,B_20] :
      ( r2_hidden(A_19,B_20)
      | v1_xboole_0(B_20)
      | ~ m1_subset_1(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_34,plain,(
    ! [A_14,B_15] : k1_enumset1(A_14,A_14,B_15) = k2_tarski(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_270,plain,(
    ! [E_107,C_108,B_109,A_110] :
      ( E_107 = C_108
      | E_107 = B_109
      | E_107 = A_110
      | ~ r2_hidden(E_107,k1_enumset1(A_110,B_109,C_108)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_303,plain,(
    ! [E_111,B_112,A_113] :
      ( E_111 = B_112
      | E_111 = A_113
      | E_111 = A_113
      | ~ r2_hidden(E_111,k2_tarski(A_113,B_112)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_270])).

tff(c_310,plain,(
    ! [B_112,A_19,A_113] :
      ( B_112 = A_19
      | A_19 = A_113
      | v1_xboole_0(k2_tarski(A_113,B_112))
      | ~ m1_subset_1(A_19,k2_tarski(A_113,B_112)) ) ),
    inference(resolution,[status(thm)],[c_38,c_303])).

tff(c_332,plain,(
    ! [B_115,A_116,A_117] :
      ( B_115 = A_116
      | A_117 = A_116
      | ~ m1_subset_1(A_116,k2_tarski(A_117,B_115)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_153,c_310])).

tff(c_335,plain,(
    ! [A_13,A_116] :
      ( A_13 = A_116
      | A_13 = A_116
      | ~ m1_subset_1(A_116,k1_tarski(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_332])).

tff(c_831,plain,(
    ! [A_174] :
      ( k1_funct_1('#skF_7',A_174) = '#skF_5'
      | ~ r2_hidden(A_174,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_827,c_335])).

tff(c_1103,plain,(
    ! [A_239] :
      ( k1_funct_1('#skF_7',A_239) = '#skF_5'
      | ~ r2_hidden(A_239,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1069,c_831])).

tff(c_1114,plain,(
    k1_funct_1('#skF_7','#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_68,c_1103])).

tff(c_1124,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1114])).

tff(c_1125,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1062])).

tff(c_14,plain,(
    ! [E_12,B_7,C_8] : r2_hidden(E_12,k1_enumset1(E_12,B_7,C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_166,plain,(
    ! [A_71,B_72] : r2_hidden(A_71,k2_tarski(A_71,B_72)) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_14])).

tff(c_178,plain,(
    ! [A_73] : r2_hidden(A_73,k1_tarski(A_73)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_166])).

tff(c_44,plain,(
    ! [B_27,A_26] :
      ( ~ r1_tarski(B_27,A_26)
      | ~ r2_hidden(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_185,plain,(
    ! [A_73] : ~ r1_tarski(k1_tarski(A_73),A_73) ),
    inference(resolution,[status(thm)],[c_178,c_44])).

tff(c_1149,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1125,c_185])).

tff(c_1159,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1149])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:15:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.43/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.43/1.58  
% 3.43/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.43/1.59  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3
% 3.43/1.59  
% 3.43/1.59  %Foreground sorts:
% 3.43/1.59  
% 3.43/1.59  
% 3.43/1.59  %Background operators:
% 3.43/1.59  
% 3.43/1.59  
% 3.43/1.59  %Foreground operators:
% 3.43/1.59  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.43/1.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.43/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.43/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.43/1.59  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.43/1.59  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.43/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.43/1.59  tff('#skF_7', type, '#skF_7': $i).
% 3.43/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.43/1.59  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.43/1.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.43/1.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.43/1.59  tff('#skF_5', type, '#skF_5': $i).
% 3.43/1.59  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.43/1.59  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.43/1.59  tff('#skF_6', type, '#skF_6': $i).
% 3.43/1.59  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.43/1.59  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.43/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.43/1.59  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.43/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.43/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.43/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.43/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.43/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.43/1.59  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.43/1.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.43/1.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.43/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.43/1.59  
% 3.43/1.60  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.43/1.60  tff(f_124, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 3.43/1.60  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.43/1.60  tff(f_113, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.43/1.60  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.43/1.60  tff(f_74, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 3.43/1.60  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.43/1.60  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.43/1.60  tff(f_66, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.43/1.60  tff(f_50, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.43/1.60  tff(f_52, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.43/1.60  tff(f_48, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 3.43/1.60  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.43/1.60  tff(f_60, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.43/1.60  tff(f_79, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.43/1.60  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.43/1.60  tff(c_66, plain, (k1_funct_1('#skF_7', '#skF_6')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.43/1.60  tff(c_68, plain, (r2_hidden('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.43/1.60  tff(c_72, plain, (v1_funct_2('#skF_7', '#skF_4', k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.43/1.60  tff(c_70, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_tarski('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.43/1.60  tff(c_261, plain, (![A_104, B_105, C_106]: (k1_relset_1(A_104, B_105, C_106)=k1_relat_1(C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.43/1.60  tff(c_265, plain, (k1_relset_1('#skF_4', k1_tarski('#skF_5'), '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_70, c_261])).
% 3.43/1.60  tff(c_1051, plain, (![B_232, A_233, C_234]: (k1_xboole_0=B_232 | k1_relset_1(A_233, B_232, C_234)=A_233 | ~v1_funct_2(C_234, A_233, B_232) | ~m1_subset_1(C_234, k1_zfmisc_1(k2_zfmisc_1(A_233, B_232))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.43/1.60  tff(c_1058, plain, (k1_tarski('#skF_5')=k1_xboole_0 | k1_relset_1('#skF_4', k1_tarski('#skF_5'), '#skF_7')='#skF_4' | ~v1_funct_2('#skF_7', '#skF_4', k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_70, c_1051])).
% 3.43/1.60  tff(c_1062, plain, (k1_tarski('#skF_5')=k1_xboole_0 | k1_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_265, c_1058])).
% 3.43/1.60  tff(c_1069, plain, (k1_relat_1('#skF_7')='#skF_4'), inference(splitLeft, [status(thm)], [c_1062])).
% 3.43/1.60  tff(c_215, plain, (![C_81, A_82, B_83]: (v1_relat_1(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.43/1.60  tff(c_219, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_70, c_215])).
% 3.43/1.60  tff(c_74, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.43/1.60  tff(c_727, plain, (![B_169, A_170]: (r2_hidden(k1_funct_1(B_169, A_170), k2_relat_1(B_169)) | ~r2_hidden(A_170, k1_relat_1(B_169)) | ~v1_funct_1(B_169) | ~v1_relat_1(B_169))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.43/1.60  tff(c_252, plain, (![A_101, B_102, C_103]: (k2_relset_1(A_101, B_102, C_103)=k2_relat_1(C_103) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.43/1.60  tff(c_256, plain, (k2_relset_1('#skF_4', k1_tarski('#skF_5'), '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_70, c_252])).
% 3.43/1.60  tff(c_356, plain, (![A_122, B_123, C_124]: (m1_subset_1(k2_relset_1(A_122, B_123, C_124), k1_zfmisc_1(B_123)) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.43/1.60  tff(c_373, plain, (m1_subset_1(k2_relat_1('#skF_7'), k1_zfmisc_1(k1_tarski('#skF_5'))) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_tarski('#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_256, c_356])).
% 3.43/1.60  tff(c_379, plain, (m1_subset_1(k2_relat_1('#skF_7'), k1_zfmisc_1(k1_tarski('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_373])).
% 3.43/1.60  tff(c_40, plain, (![A_21, C_23, B_22]: (m1_subset_1(A_21, C_23) | ~m1_subset_1(B_22, k1_zfmisc_1(C_23)) | ~r2_hidden(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.43/1.60  tff(c_400, plain, (![A_21]: (m1_subset_1(A_21, k1_tarski('#skF_5')) | ~r2_hidden(A_21, k2_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_379, c_40])).
% 3.43/1.60  tff(c_731, plain, (![A_170]: (m1_subset_1(k1_funct_1('#skF_7', A_170), k1_tarski('#skF_5')) | ~r2_hidden(A_170, k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_727, c_400])).
% 3.43/1.60  tff(c_827, plain, (![A_174]: (m1_subset_1(k1_funct_1('#skF_7', A_174), k1_tarski('#skF_5')) | ~r2_hidden(A_174, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_219, c_74, c_731])).
% 3.43/1.60  tff(c_32, plain, (![A_13]: (k2_tarski(A_13, A_13)=k1_tarski(A_13))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.43/1.60  tff(c_139, plain, (![A_66, B_67]: (k1_enumset1(A_66, A_66, B_67)=k2_tarski(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.43/1.60  tff(c_90, plain, (![E_47, A_48, C_49]: (r2_hidden(E_47, k1_enumset1(A_48, E_47, C_49)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.43/1.60  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.43/1.60  tff(c_94, plain, (![A_48, E_47, C_49]: (~v1_xboole_0(k1_enumset1(A_48, E_47, C_49)))), inference(resolution, [status(thm)], [c_90, c_2])).
% 3.43/1.60  tff(c_153, plain, (![A_66, B_67]: (~v1_xboole_0(k2_tarski(A_66, B_67)))), inference(superposition, [status(thm), theory('equality')], [c_139, c_94])).
% 3.43/1.60  tff(c_38, plain, (![A_19, B_20]: (r2_hidden(A_19, B_20) | v1_xboole_0(B_20) | ~m1_subset_1(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.43/1.60  tff(c_34, plain, (![A_14, B_15]: (k1_enumset1(A_14, A_14, B_15)=k2_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.43/1.60  tff(c_270, plain, (![E_107, C_108, B_109, A_110]: (E_107=C_108 | E_107=B_109 | E_107=A_110 | ~r2_hidden(E_107, k1_enumset1(A_110, B_109, C_108)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.43/1.60  tff(c_303, plain, (![E_111, B_112, A_113]: (E_111=B_112 | E_111=A_113 | E_111=A_113 | ~r2_hidden(E_111, k2_tarski(A_113, B_112)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_270])).
% 3.43/1.60  tff(c_310, plain, (![B_112, A_19, A_113]: (B_112=A_19 | A_19=A_113 | v1_xboole_0(k2_tarski(A_113, B_112)) | ~m1_subset_1(A_19, k2_tarski(A_113, B_112)))), inference(resolution, [status(thm)], [c_38, c_303])).
% 3.43/1.60  tff(c_332, plain, (![B_115, A_116, A_117]: (B_115=A_116 | A_117=A_116 | ~m1_subset_1(A_116, k2_tarski(A_117, B_115)))), inference(negUnitSimplification, [status(thm)], [c_153, c_310])).
% 3.43/1.60  tff(c_335, plain, (![A_13, A_116]: (A_13=A_116 | A_13=A_116 | ~m1_subset_1(A_116, k1_tarski(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_332])).
% 3.43/1.60  tff(c_831, plain, (![A_174]: (k1_funct_1('#skF_7', A_174)='#skF_5' | ~r2_hidden(A_174, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_827, c_335])).
% 3.43/1.60  tff(c_1103, plain, (![A_239]: (k1_funct_1('#skF_7', A_239)='#skF_5' | ~r2_hidden(A_239, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1069, c_831])).
% 3.43/1.60  tff(c_1114, plain, (k1_funct_1('#skF_7', '#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_68, c_1103])).
% 3.43/1.60  tff(c_1124, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_1114])).
% 3.43/1.60  tff(c_1125, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1062])).
% 3.43/1.60  tff(c_14, plain, (![E_12, B_7, C_8]: (r2_hidden(E_12, k1_enumset1(E_12, B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.43/1.60  tff(c_166, plain, (![A_71, B_72]: (r2_hidden(A_71, k2_tarski(A_71, B_72)))), inference(superposition, [status(thm), theory('equality')], [c_139, c_14])).
% 3.43/1.60  tff(c_178, plain, (![A_73]: (r2_hidden(A_73, k1_tarski(A_73)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_166])).
% 3.43/1.60  tff(c_44, plain, (![B_27, A_26]: (~r1_tarski(B_27, A_26) | ~r2_hidden(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.43/1.60  tff(c_185, plain, (![A_73]: (~r1_tarski(k1_tarski(A_73), A_73))), inference(resolution, [status(thm)], [c_178, c_44])).
% 3.43/1.60  tff(c_1149, plain, (~r1_tarski(k1_xboole_0, '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1125, c_185])).
% 3.43/1.60  tff(c_1159, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1149])).
% 3.43/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.43/1.60  
% 3.43/1.60  Inference rules
% 3.43/1.60  ----------------------
% 3.43/1.60  #Ref     : 0
% 3.43/1.60  #Sup     : 218
% 3.43/1.60  #Fact    : 4
% 3.43/1.60  #Define  : 0
% 3.43/1.60  #Split   : 9
% 3.43/1.60  #Chain   : 0
% 3.43/1.60  #Close   : 0
% 3.43/1.60  
% 3.43/1.60  Ordering : KBO
% 3.43/1.60  
% 3.43/1.60  Simplification rules
% 3.43/1.60  ----------------------
% 3.43/1.60  #Subsume      : 40
% 3.43/1.60  #Demod        : 120
% 3.43/1.60  #Tautology    : 72
% 3.43/1.60  #SimpNegUnit  : 28
% 3.43/1.60  #BackRed      : 43
% 3.43/1.60  
% 3.43/1.60  #Partial instantiations: 0
% 3.43/1.60  #Strategies tried      : 1
% 3.43/1.60  
% 3.43/1.60  Timing (in seconds)
% 3.43/1.60  ----------------------
% 3.43/1.61  Preprocessing        : 0.35
% 3.43/1.61  Parsing              : 0.18
% 3.43/1.61  CNF conversion       : 0.03
% 3.43/1.61  Main loop            : 0.44
% 3.43/1.61  Inferencing          : 0.16
% 3.43/1.61  Reduction            : 0.14
% 3.43/1.61  Demodulation         : 0.09
% 3.43/1.61  BG Simplification    : 0.02
% 3.43/1.61  Subsumption          : 0.08
% 3.43/1.61  Abstraction          : 0.03
% 3.43/1.61  MUC search           : 0.00
% 3.43/1.61  Cooper               : 0.00
% 3.43/1.61  Total                : 0.82
% 3.43/1.61  Index Insertion      : 0.00
% 3.43/1.61  Index Deletion       : 0.00
% 3.43/1.61  Index Matching       : 0.00
% 3.43/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
