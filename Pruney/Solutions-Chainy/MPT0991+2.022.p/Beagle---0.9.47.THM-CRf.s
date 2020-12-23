%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:29 EST 2020

% Result     : Theorem 3.69s
% Output     : CNFRefutation 3.69s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 180 expanded)
%              Number of leaves         :   49 (  85 expanded)
%              Depth                    :   12
%              Number of atoms          :  198 ( 520 expanded)
%              Number of equality atoms :   51 (  98 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_168,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ~ ( B != k1_xboole_0
            & ? [D] :
                ( v1_funct_1(D)
                & v1_funct_2(D,B,A)
                & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A)))
                & r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A)) )
            & ~ v2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_145,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_77,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_129,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_133,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_99,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_143,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_117,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(k5_relat_1(B,A))
              & r1_tarski(k2_relat_1(B),k1_relat_1(A)) )
           => v2_funct_1(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_funct_1)).

tff(f_60,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( ! [B] :
            ~ ( r2_hidden(B,k2_relat_1(A))
              & ! [C] : k10_relat_1(A,k1_tarski(B)) != k1_tarski(C) )
      <=> v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_funct_1)).

tff(c_64,plain,(
    ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_119,plain,(
    ! [A_59,B_60] : ~ r2_hidden(A_59,k2_zfmisc_1(A_59,B_60)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_125,plain,(
    ! [A_1] : ~ r2_hidden(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_119])).

tff(c_76,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_137,plain,(
    ! [C_63,A_64,B_65] :
      ( v1_relat_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_153,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_137])).

tff(c_80,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_264,plain,(
    ! [C_85,B_86,A_87] :
      ( v5_relat_1(C_85,B_86)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_87,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_282,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_264])).

tff(c_62,plain,(
    ! [A_52] : k6_relat_1(A_52) = k6_partfun1(A_52) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_26,plain,(
    ! [A_22] : v2_funct_1(k6_relat_1(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_81,plain,(
    ! [A_22] : v2_funct_1(k6_partfun1(A_22)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_26])).

tff(c_72,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_68,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_740,plain,(
    ! [E_178,B_174,D_176,F_177,C_175,A_173] :
      ( m1_subset_1(k1_partfun1(A_173,B_174,C_175,D_176,E_178,F_177),k1_zfmisc_1(k2_zfmisc_1(A_173,D_176)))
      | ~ m1_subset_1(F_177,k1_zfmisc_1(k2_zfmisc_1(C_175,D_176)))
      | ~ v1_funct_1(F_177)
      | ~ m1_subset_1(E_178,k1_zfmisc_1(k2_zfmisc_1(A_173,B_174)))
      | ~ v1_funct_1(E_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_58,plain,(
    ! [A_45] : m1_subset_1(k6_partfun1(A_45),k1_zfmisc_1(k2_zfmisc_1(A_45,A_45))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_66,plain,(
    r2_relset_1('#skF_3','#skF_3',k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k6_partfun1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_566,plain,(
    ! [D_141,C_142,A_143,B_144] :
      ( D_141 = C_142
      | ~ r2_relset_1(A_143,B_144,C_142,D_141)
      | ~ m1_subset_1(D_141,k1_zfmisc_1(k2_zfmisc_1(A_143,B_144)))
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(A_143,B_144))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_578,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3')
    | ~ m1_subset_1(k6_partfun1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_66,c_566])).

tff(c_601,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3')
    | ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_578])).

tff(c_646,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_601])).

tff(c_753,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_740,c_646])).

tff(c_787,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_72,c_68,c_753])).

tff(c_788,plain,(
    k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_601])).

tff(c_844,plain,(
    ! [F_192,B_191,C_195,D_193,E_194,A_196] :
      ( k1_partfun1(A_196,B_191,C_195,D_193,E_194,F_192) = k5_relat_1(E_194,F_192)
      | ~ m1_subset_1(F_192,k1_zfmisc_1(k2_zfmisc_1(C_195,D_193)))
      | ~ v1_funct_1(F_192)
      | ~ m1_subset_1(E_194,k1_zfmisc_1(k2_zfmisc_1(A_196,B_191)))
      | ~ v1_funct_1(E_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_848,plain,(
    ! [A_196,B_191,E_194] :
      ( k1_partfun1(A_196,B_191,'#skF_4','#skF_3',E_194,'#skF_6') = k5_relat_1(E_194,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_194,k1_zfmisc_1(k2_zfmisc_1(A_196,B_191)))
      | ~ v1_funct_1(E_194) ) ),
    inference(resolution,[status(thm)],[c_68,c_844])).

tff(c_1064,plain,(
    ! [A_216,B_217,E_218] :
      ( k1_partfun1(A_216,B_217,'#skF_4','#skF_3',E_218,'#skF_6') = k5_relat_1(E_218,'#skF_6')
      | ~ m1_subset_1(E_218,k1_zfmisc_1(k2_zfmisc_1(A_216,B_217)))
      | ~ v1_funct_1(E_218) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_848])).

tff(c_1082,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_1064])).

tff(c_1096,plain,(
    k5_relat_1('#skF_5','#skF_6') = k6_partfun1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_788,c_1082])).

tff(c_12,plain,(
    ! [B_6,A_5] :
      ( r1_tarski(k2_relat_1(B_6),A_5)
      | ~ v5_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_152,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_137])).

tff(c_74,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_78,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_324,plain,(
    ! [A_106,B_107,C_108] :
      ( k1_relset_1(A_106,B_107,C_108) = k1_relat_1(C_108)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_342,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_324])).

tff(c_471,plain,(
    ! [B_131,A_132,C_133] :
      ( k1_xboole_0 = B_131
      | k1_relset_1(A_132,B_131,C_133) = A_132
      | ~ v1_funct_2(C_133,A_132,B_131)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_132,B_131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_483,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_471])).

tff(c_494,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_342,c_483])).

tff(c_495,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_494])).

tff(c_161,plain,(
    ! [A_68] :
      ( k2_relat_1(A_68) = k1_xboole_0
      | k1_relat_1(A_68) != k1_xboole_0
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_172,plain,
    ( k2_relat_1('#skF_5') = k1_xboole_0
    | k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_153,c_161])).

tff(c_174,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_172])).

tff(c_508,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_495,c_174])).

tff(c_70,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_341,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_324])).

tff(c_477,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_4','#skF_3','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_471])).

tff(c_491,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_341,c_477])).

tff(c_513,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_508,c_491])).

tff(c_533,plain,(
    ! [B_137,A_138] :
      ( v2_funct_1(B_137)
      | ~ r1_tarski(k2_relat_1(B_137),k1_relat_1(A_138))
      | ~ v2_funct_1(k5_relat_1(B_137,A_138))
      | ~ v1_funct_1(B_137)
      | ~ v1_relat_1(B_137)
      | ~ v1_funct_1(A_138)
      | ~ v1_relat_1(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_536,plain,(
    ! [B_137] :
      ( v2_funct_1(B_137)
      | ~ r1_tarski(k2_relat_1(B_137),'#skF_4')
      | ~ v2_funct_1(k5_relat_1(B_137,'#skF_6'))
      | ~ v1_funct_1(B_137)
      | ~ v1_relat_1(B_137)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_513,c_533])).

tff(c_602,plain,(
    ! [B_145] :
      ( v2_funct_1(B_145)
      | ~ r1_tarski(k2_relat_1(B_145),'#skF_4')
      | ~ v2_funct_1(k5_relat_1(B_145,'#skF_6'))
      | ~ v1_funct_1(B_145)
      | ~ v1_relat_1(B_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_72,c_536])).

tff(c_612,plain,(
    ! [B_6] :
      ( v2_funct_1(B_6)
      | ~ v2_funct_1(k5_relat_1(B_6,'#skF_6'))
      | ~ v1_funct_1(B_6)
      | ~ v5_relat_1(B_6,'#skF_4')
      | ~ v1_relat_1(B_6) ) ),
    inference(resolution,[status(thm)],[c_12,c_602])).

tff(c_1100,plain,
    ( v2_funct_1('#skF_5')
    | ~ v2_funct_1(k6_partfun1('#skF_3'))
    | ~ v1_funct_1('#skF_5')
    | ~ v5_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1096,c_612])).

tff(c_1104,plain,(
    v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_282,c_80,c_81,c_1100])).

tff(c_1106,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1104])).

tff(c_1107,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_1266,plain,(
    ! [A_247] :
      ( r2_hidden('#skF_1'(A_247),k2_relat_1(A_247))
      | v2_funct_1(A_247)
      | ~ v1_funct_1(A_247)
      | ~ v1_relat_1(A_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1272,plain,
    ( r2_hidden('#skF_1'('#skF_5'),k1_xboole_0)
    | v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1107,c_1266])).

tff(c_1277,plain,
    ( r2_hidden('#skF_1'('#skF_5'),k1_xboole_0)
    | v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_80,c_1272])).

tff(c_1279,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_125,c_1277])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:48:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.69/1.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.69/1.62  
% 3.69/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.69/1.63  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 3.69/1.63  
% 3.69/1.63  %Foreground sorts:
% 3.69/1.63  
% 3.69/1.63  
% 3.69/1.63  %Background operators:
% 3.69/1.63  
% 3.69/1.63  
% 3.69/1.63  %Foreground operators:
% 3.69/1.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.69/1.63  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.69/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.69/1.63  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.69/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.69/1.63  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.69/1.63  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.69/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.69/1.63  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.69/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.69/1.63  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.69/1.63  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.69/1.63  tff('#skF_5', type, '#skF_5': $i).
% 3.69/1.63  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.69/1.63  tff('#skF_6', type, '#skF_6': $i).
% 3.69/1.63  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.69/1.63  tff('#skF_3', type, '#skF_3': $i).
% 3.69/1.63  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.69/1.63  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.69/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.69/1.63  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.69/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.69/1.63  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.69/1.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.69/1.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.69/1.63  tff('#skF_4', type, '#skF_4': $i).
% 3.69/1.63  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.69/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.69/1.63  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.69/1.63  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.69/1.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.69/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.69/1.63  
% 3.69/1.64  tff(f_168, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~((~(B = k1_xboole_0) & (?[D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))))) & ~v2_funct_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_funct_2)).
% 3.69/1.64  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.69/1.64  tff(f_34, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 3.69/1.64  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.69/1.64  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.69/1.64  tff(f_145, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.69/1.64  tff(f_77, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_funct_1)).
% 3.69/1.64  tff(f_129, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 3.69/1.64  tff(f_133, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 3.69/1.64  tff(f_99, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.69/1.64  tff(f_143, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.69/1.64  tff(f_40, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.69/1.64  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.69/1.64  tff(f_117, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.69/1.64  tff(f_46, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 3.69/1.64  tff(f_75, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & r1_tarski(k2_relat_1(B), k1_relat_1(A))) => v2_funct_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_funct_1)).
% 3.69/1.64  tff(f_60, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((![B]: ~(r2_hidden(B, k2_relat_1(A)) & (![C]: ~(k10_relat_1(A, k1_tarski(B)) = k1_tarski(C))))) <=> v2_funct_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_funct_1)).
% 3.69/1.64  tff(c_64, plain, (~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.69/1.64  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.69/1.64  tff(c_119, plain, (![A_59, B_60]: (~r2_hidden(A_59, k2_zfmisc_1(A_59, B_60)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.69/1.64  tff(c_125, plain, (![A_1]: (~r2_hidden(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_119])).
% 3.69/1.64  tff(c_76, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.69/1.64  tff(c_137, plain, (![C_63, A_64, B_65]: (v1_relat_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.69/1.64  tff(c_153, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_76, c_137])).
% 3.69/1.64  tff(c_80, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.69/1.64  tff(c_264, plain, (![C_85, B_86, A_87]: (v5_relat_1(C_85, B_86) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_87, B_86))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.69/1.64  tff(c_282, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_76, c_264])).
% 3.69/1.64  tff(c_62, plain, (![A_52]: (k6_relat_1(A_52)=k6_partfun1(A_52))), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.69/1.64  tff(c_26, plain, (![A_22]: (v2_funct_1(k6_relat_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.69/1.64  tff(c_81, plain, (![A_22]: (v2_funct_1(k6_partfun1(A_22)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_26])).
% 3.69/1.64  tff(c_72, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.69/1.64  tff(c_68, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.69/1.64  tff(c_740, plain, (![E_178, B_174, D_176, F_177, C_175, A_173]: (m1_subset_1(k1_partfun1(A_173, B_174, C_175, D_176, E_178, F_177), k1_zfmisc_1(k2_zfmisc_1(A_173, D_176))) | ~m1_subset_1(F_177, k1_zfmisc_1(k2_zfmisc_1(C_175, D_176))) | ~v1_funct_1(F_177) | ~m1_subset_1(E_178, k1_zfmisc_1(k2_zfmisc_1(A_173, B_174))) | ~v1_funct_1(E_178))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.69/1.64  tff(c_58, plain, (![A_45]: (m1_subset_1(k6_partfun1(A_45), k1_zfmisc_1(k2_zfmisc_1(A_45, A_45))))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.69/1.64  tff(c_66, plain, (r2_relset_1('#skF_3', '#skF_3', k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k6_partfun1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.69/1.64  tff(c_566, plain, (![D_141, C_142, A_143, B_144]: (D_141=C_142 | ~r2_relset_1(A_143, B_144, C_142, D_141) | ~m1_subset_1(D_141, k1_zfmisc_1(k2_zfmisc_1(A_143, B_144))) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(A_143, B_144))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.69/1.64  tff(c_578, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3') | ~m1_subset_1(k6_partfun1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(resolution, [status(thm)], [c_66, c_566])).
% 3.69/1.64  tff(c_601, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3') | ~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_578])).
% 3.69/1.64  tff(c_646, plain, (~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(splitLeft, [status(thm)], [c_601])).
% 3.69/1.64  tff(c_753, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_740, c_646])).
% 3.69/1.64  tff(c_787, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_72, c_68, c_753])).
% 3.69/1.64  tff(c_788, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3')), inference(splitRight, [status(thm)], [c_601])).
% 3.69/1.64  tff(c_844, plain, (![F_192, B_191, C_195, D_193, E_194, A_196]: (k1_partfun1(A_196, B_191, C_195, D_193, E_194, F_192)=k5_relat_1(E_194, F_192) | ~m1_subset_1(F_192, k1_zfmisc_1(k2_zfmisc_1(C_195, D_193))) | ~v1_funct_1(F_192) | ~m1_subset_1(E_194, k1_zfmisc_1(k2_zfmisc_1(A_196, B_191))) | ~v1_funct_1(E_194))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.69/1.64  tff(c_848, plain, (![A_196, B_191, E_194]: (k1_partfun1(A_196, B_191, '#skF_4', '#skF_3', E_194, '#skF_6')=k5_relat_1(E_194, '#skF_6') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_194, k1_zfmisc_1(k2_zfmisc_1(A_196, B_191))) | ~v1_funct_1(E_194))), inference(resolution, [status(thm)], [c_68, c_844])).
% 3.69/1.64  tff(c_1064, plain, (![A_216, B_217, E_218]: (k1_partfun1(A_216, B_217, '#skF_4', '#skF_3', E_218, '#skF_6')=k5_relat_1(E_218, '#skF_6') | ~m1_subset_1(E_218, k1_zfmisc_1(k2_zfmisc_1(A_216, B_217))) | ~v1_funct_1(E_218))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_848])).
% 3.69/1.64  tff(c_1082, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_76, c_1064])).
% 3.69/1.64  tff(c_1096, plain, (k5_relat_1('#skF_5', '#skF_6')=k6_partfun1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_788, c_1082])).
% 3.69/1.64  tff(c_12, plain, (![B_6, A_5]: (r1_tarski(k2_relat_1(B_6), A_5) | ~v5_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.69/1.64  tff(c_152, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_68, c_137])).
% 3.69/1.64  tff(c_74, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.69/1.64  tff(c_78, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.69/1.64  tff(c_324, plain, (![A_106, B_107, C_108]: (k1_relset_1(A_106, B_107, C_108)=k1_relat_1(C_108) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.69/1.64  tff(c_342, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_76, c_324])).
% 3.69/1.64  tff(c_471, plain, (![B_131, A_132, C_133]: (k1_xboole_0=B_131 | k1_relset_1(A_132, B_131, C_133)=A_132 | ~v1_funct_2(C_133, A_132, B_131) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_132, B_131))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.69/1.64  tff(c_483, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_76, c_471])).
% 3.69/1.64  tff(c_494, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_342, c_483])).
% 3.69/1.64  tff(c_495, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_74, c_494])).
% 3.69/1.64  tff(c_161, plain, (![A_68]: (k2_relat_1(A_68)=k1_xboole_0 | k1_relat_1(A_68)!=k1_xboole_0 | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.69/1.64  tff(c_172, plain, (k2_relat_1('#skF_5')=k1_xboole_0 | k1_relat_1('#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_153, c_161])).
% 3.69/1.64  tff(c_174, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_172])).
% 3.69/1.64  tff(c_508, plain, (k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_495, c_174])).
% 3.69/1.64  tff(c_70, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.69/1.64  tff(c_341, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_68, c_324])).
% 3.69/1.64  tff(c_477, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_4', '#skF_3', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_68, c_471])).
% 3.69/1.64  tff(c_491, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_341, c_477])).
% 3.69/1.64  tff(c_513, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_508, c_491])).
% 3.69/1.64  tff(c_533, plain, (![B_137, A_138]: (v2_funct_1(B_137) | ~r1_tarski(k2_relat_1(B_137), k1_relat_1(A_138)) | ~v2_funct_1(k5_relat_1(B_137, A_138)) | ~v1_funct_1(B_137) | ~v1_relat_1(B_137) | ~v1_funct_1(A_138) | ~v1_relat_1(A_138))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.69/1.64  tff(c_536, plain, (![B_137]: (v2_funct_1(B_137) | ~r1_tarski(k2_relat_1(B_137), '#skF_4') | ~v2_funct_1(k5_relat_1(B_137, '#skF_6')) | ~v1_funct_1(B_137) | ~v1_relat_1(B_137) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_513, c_533])).
% 3.69/1.64  tff(c_602, plain, (![B_145]: (v2_funct_1(B_145) | ~r1_tarski(k2_relat_1(B_145), '#skF_4') | ~v2_funct_1(k5_relat_1(B_145, '#skF_6')) | ~v1_funct_1(B_145) | ~v1_relat_1(B_145))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_72, c_536])).
% 3.69/1.64  tff(c_612, plain, (![B_6]: (v2_funct_1(B_6) | ~v2_funct_1(k5_relat_1(B_6, '#skF_6')) | ~v1_funct_1(B_6) | ~v5_relat_1(B_6, '#skF_4') | ~v1_relat_1(B_6))), inference(resolution, [status(thm)], [c_12, c_602])).
% 3.69/1.64  tff(c_1100, plain, (v2_funct_1('#skF_5') | ~v2_funct_1(k6_partfun1('#skF_3')) | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1096, c_612])).
% 3.69/1.64  tff(c_1104, plain, (v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_153, c_282, c_80, c_81, c_1100])).
% 3.69/1.64  tff(c_1106, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_1104])).
% 3.69/1.64  tff(c_1107, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_172])).
% 3.69/1.64  tff(c_1266, plain, (![A_247]: (r2_hidden('#skF_1'(A_247), k2_relat_1(A_247)) | v2_funct_1(A_247) | ~v1_funct_1(A_247) | ~v1_relat_1(A_247))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.69/1.64  tff(c_1272, plain, (r2_hidden('#skF_1'('#skF_5'), k1_xboole_0) | v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1107, c_1266])).
% 3.69/1.64  tff(c_1277, plain, (r2_hidden('#skF_1'('#skF_5'), k1_xboole_0) | v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_153, c_80, c_1272])).
% 3.69/1.64  tff(c_1279, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_125, c_1277])).
% 3.69/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.69/1.64  
% 3.69/1.64  Inference rules
% 3.69/1.64  ----------------------
% 3.69/1.64  #Ref     : 0
% 3.69/1.64  #Sup     : 271
% 3.69/1.64  #Fact    : 0
% 3.69/1.64  #Define  : 0
% 3.69/1.64  #Split   : 10
% 3.69/1.64  #Chain   : 0
% 3.69/1.64  #Close   : 0
% 3.69/1.64  
% 3.69/1.64  Ordering : KBO
% 3.69/1.64  
% 3.69/1.64  Simplification rules
% 3.69/1.65  ----------------------
% 3.69/1.65  #Subsume      : 19
% 3.69/1.65  #Demod        : 124
% 3.69/1.65  #Tautology    : 83
% 3.69/1.65  #SimpNegUnit  : 13
% 3.69/1.65  #BackRed      : 6
% 3.69/1.65  
% 3.69/1.65  #Partial instantiations: 0
% 3.69/1.65  #Strategies tried      : 1
% 3.69/1.65  
% 3.69/1.65  Timing (in seconds)
% 3.69/1.65  ----------------------
% 3.69/1.65  Preprocessing        : 0.37
% 3.69/1.65  Parsing              : 0.20
% 3.69/1.65  CNF conversion       : 0.03
% 3.69/1.65  Main loop            : 0.50
% 3.69/1.65  Inferencing          : 0.18
% 3.69/1.65  Reduction            : 0.17
% 3.69/1.65  Demodulation         : 0.11
% 3.69/1.65  BG Simplification    : 0.03
% 3.69/1.65  Subsumption          : 0.08
% 3.69/1.65  Abstraction          : 0.02
% 3.69/1.65  MUC search           : 0.00
% 3.69/1.65  Cooper               : 0.00
% 3.69/1.65  Total                : 0.91
% 3.69/1.65  Index Insertion      : 0.00
% 3.69/1.65  Index Deletion       : 0.00
% 3.69/1.65  Index Matching       : 0.00
% 3.69/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
