%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:29 EST 2020

% Result     : Theorem 4.21s
% Output     : CNFRefutation 4.51s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 199 expanded)
%              Number of leaves         :   49 (  92 expanded)
%              Depth                    :   12
%              Number of atoms          :  199 ( 615 expanded)
%              Number of equality atoms :   51 ( 113 expanded)
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

tff(f_170,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_147,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_145,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_131,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_135,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_101,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_119,axiom,(
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

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_79,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(k5_relat_1(B,A))
              & r1_tarski(k2_relat_1(B),k1_relat_1(A)) )
           => v2_funct_1(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_funct_1)).

tff(f_64,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( ! [B] :
            ~ ( r2_hidden(B,k2_relat_1(A))
              & ! [C] : k10_relat_1(A,k1_tarski(B)) != k1_tarski(C) )
      <=> v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_funct_1)).

tff(c_66,plain,(
    ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_123,plain,(
    ! [A_60,B_61] : ~ r2_hidden(A_60,k2_zfmisc_1(A_60,B_61)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_129,plain,(
    ! [A_1] : ~ r2_hidden(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_123])).

tff(c_78,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_141,plain,(
    ! [C_64,A_65,B_66] :
      ( v1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_158,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_78,c_141])).

tff(c_82,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_228,plain,(
    ! [C_76,B_77,A_78] :
      ( v5_relat_1(C_76,B_77)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_78,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_246,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_228])).

tff(c_64,plain,(
    ! [A_52] : k6_relat_1(A_52) = k6_partfun1(A_52) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_20,plain,(
    ! [A_8] : v2_funct_1(k6_relat_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_83,plain,(
    ! [A_8] : v2_funct_1(k6_partfun1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_20])).

tff(c_74,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_70,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_667,plain,(
    ! [E_162,B_159,D_161,C_163,A_164,F_160] :
      ( k1_partfun1(A_164,B_159,C_163,D_161,E_162,F_160) = k5_relat_1(E_162,F_160)
      | ~ m1_subset_1(F_160,k1_zfmisc_1(k2_zfmisc_1(C_163,D_161)))
      | ~ v1_funct_1(F_160)
      | ~ m1_subset_1(E_162,k1_zfmisc_1(k2_zfmisc_1(A_164,B_159)))
      | ~ v1_funct_1(E_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_671,plain,(
    ! [A_164,B_159,E_162] :
      ( k1_partfun1(A_164,B_159,'#skF_4','#skF_3',E_162,'#skF_6') = k5_relat_1(E_162,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_162,k1_zfmisc_1(k2_zfmisc_1(A_164,B_159)))
      | ~ v1_funct_1(E_162) ) ),
    inference(resolution,[status(thm)],[c_70,c_667])).

tff(c_886,plain,(
    ! [A_184,B_185,E_186] :
      ( k1_partfun1(A_184,B_185,'#skF_4','#skF_3',E_186,'#skF_6') = k5_relat_1(E_186,'#skF_6')
      | ~ m1_subset_1(E_186,k1_zfmisc_1(k2_zfmisc_1(A_184,B_185)))
      | ~ v1_funct_1(E_186) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_671])).

tff(c_901,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_78,c_886])).

tff(c_918,plain,(
    k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_901])).

tff(c_54,plain,(
    ! [E_43,F_44,D_42,A_39,C_41,B_40] :
      ( m1_subset_1(k1_partfun1(A_39,B_40,C_41,D_42,E_43,F_44),k1_zfmisc_1(k2_zfmisc_1(A_39,D_42)))
      | ~ m1_subset_1(F_44,k1_zfmisc_1(k2_zfmisc_1(C_41,D_42)))
      | ~ v1_funct_1(F_44)
      | ~ m1_subset_1(E_43,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40)))
      | ~ v1_funct_1(E_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1132,plain,
    ( m1_subset_1(k5_relat_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_918,c_54])).

tff(c_1136,plain,(
    m1_subset_1(k5_relat_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_74,c_70,c_1132])).

tff(c_60,plain,(
    ! [A_45] : m1_subset_1(k6_partfun1(A_45),k1_zfmisc_1(k2_zfmisc_1(A_45,A_45))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_68,plain,(
    r2_relset_1('#skF_3','#skF_3',k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k6_partfun1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_540,plain,(
    ! [D_137,C_138,A_139,B_140] :
      ( D_137 = C_138
      | ~ r2_relset_1(A_139,B_140,C_138,D_137)
      | ~ m1_subset_1(D_137,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140)))
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_552,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3')
    | ~ m1_subset_1(k6_partfun1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_68,c_540])).

tff(c_575,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3')
    | ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_552])).

tff(c_1265,plain,(
    k5_relat_1('#skF_5','#skF_6') = k6_partfun1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1136,c_918,c_918,c_575])).

tff(c_12,plain,(
    ! [B_6,A_5] :
      ( r1_tarski(k2_relat_1(B_6),A_5)
      | ~ v5_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_157,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_141])).

tff(c_76,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_80,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_316,plain,(
    ! [A_97,B_98,C_99] :
      ( k1_relset_1(A_97,B_98,C_99) = k1_relat_1(C_99)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_334,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_78,c_316])).

tff(c_431,plain,(
    ! [B_123,A_124,C_125] :
      ( k1_xboole_0 = B_123
      | k1_relset_1(A_124,B_123,C_125) = A_124
      | ~ v1_funct_2(C_125,A_124,B_123)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_124,B_123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_440,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_431])).

tff(c_454,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_334,c_440])).

tff(c_455,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_454])).

tff(c_176,plain,(
    ! [A_70] :
      ( k2_relat_1(A_70) = k1_xboole_0
      | k1_relat_1(A_70) != k1_xboole_0
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_186,plain,
    ( k2_relat_1('#skF_5') = k1_xboole_0
    | k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_158,c_176])).

tff(c_189,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_186])).

tff(c_458,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_455,c_189])).

tff(c_72,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_333,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_316])).

tff(c_437,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_4','#skF_3','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_431])).

tff(c_451,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_333,c_437])).

tff(c_463,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_458,c_451])).

tff(c_576,plain,(
    ! [B_141,A_142] :
      ( v2_funct_1(B_141)
      | ~ r1_tarski(k2_relat_1(B_141),k1_relat_1(A_142))
      | ~ v2_funct_1(k5_relat_1(B_141,A_142))
      | ~ v1_funct_1(B_141)
      | ~ v1_relat_1(B_141)
      | ~ v1_funct_1(A_142)
      | ~ v1_relat_1(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_579,plain,(
    ! [B_141] :
      ( v2_funct_1(B_141)
      | ~ r1_tarski(k2_relat_1(B_141),'#skF_4')
      | ~ v2_funct_1(k5_relat_1(B_141,'#skF_6'))
      | ~ v1_funct_1(B_141)
      | ~ v1_relat_1(B_141)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_463,c_576])).

tff(c_627,plain,(
    ! [B_151] :
      ( v2_funct_1(B_151)
      | ~ r1_tarski(k2_relat_1(B_151),'#skF_4')
      | ~ v2_funct_1(k5_relat_1(B_151,'#skF_6'))
      | ~ v1_funct_1(B_151)
      | ~ v1_relat_1(B_151) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_74,c_579])).

tff(c_637,plain,(
    ! [B_6] :
      ( v2_funct_1(B_6)
      | ~ v2_funct_1(k5_relat_1(B_6,'#skF_6'))
      | ~ v1_funct_1(B_6)
      | ~ v5_relat_1(B_6,'#skF_4')
      | ~ v1_relat_1(B_6) ) ),
    inference(resolution,[status(thm)],[c_12,c_627])).

tff(c_1284,plain,
    ( v2_funct_1('#skF_5')
    | ~ v2_funct_1(k6_partfun1('#skF_3'))
    | ~ v1_funct_1('#skF_5')
    | ~ v5_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1265,c_637])).

tff(c_1288,plain,(
    v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_246,c_82,c_83,c_1284])).

tff(c_1290,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1288])).

tff(c_1291,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_1419,plain,(
    ! [A_213] :
      ( r2_hidden('#skF_1'(A_213),k2_relat_1(A_213))
      | v2_funct_1(A_213)
      | ~ v1_funct_1(A_213)
      | ~ v1_relat_1(A_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1425,plain,
    ( r2_hidden('#skF_1'('#skF_5'),k1_xboole_0)
    | v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1291,c_1419])).

tff(c_1430,plain,
    ( r2_hidden('#skF_1'('#skF_5'),k1_xboole_0)
    | v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_82,c_1425])).

tff(c_1432,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_129,c_1430])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:45:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.21/1.80  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.39/1.82  
% 4.39/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.39/1.82  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 4.39/1.82  
% 4.39/1.82  %Foreground sorts:
% 4.39/1.82  
% 4.39/1.82  
% 4.39/1.82  %Background operators:
% 4.39/1.82  
% 4.39/1.82  
% 4.39/1.82  %Foreground operators:
% 4.39/1.82  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.39/1.82  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.39/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.39/1.82  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.39/1.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.39/1.82  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.39/1.82  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.39/1.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.39/1.82  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.39/1.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.39/1.82  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.39/1.82  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.39/1.82  tff('#skF_5', type, '#skF_5': $i).
% 4.39/1.82  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.39/1.82  tff('#skF_6', type, '#skF_6': $i).
% 4.39/1.82  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.39/1.82  tff('#skF_3', type, '#skF_3': $i).
% 4.39/1.82  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.39/1.82  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.39/1.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.39/1.82  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.39/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.39/1.82  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.39/1.82  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.39/1.82  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.39/1.82  tff('#skF_4', type, '#skF_4': $i).
% 4.39/1.82  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.39/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.39/1.82  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.39/1.82  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.39/1.82  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.39/1.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.39/1.82  
% 4.51/1.84  tff(f_170, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~((~(B = k1_xboole_0) & (?[D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))))) & ~v2_funct_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_funct_2)).
% 4.51/1.84  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.51/1.84  tff(f_34, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 4.51/1.84  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.51/1.84  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.51/1.84  tff(f_147, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.51/1.84  tff(f_50, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 4.51/1.84  tff(f_145, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 4.51/1.84  tff(f_131, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 4.51/1.84  tff(f_135, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 4.51/1.84  tff(f_101, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.51/1.84  tff(f_40, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 4.51/1.84  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.51/1.84  tff(f_119, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.51/1.84  tff(f_46, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 4.51/1.84  tff(f_79, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & r1_tarski(k2_relat_1(B), k1_relat_1(A))) => v2_funct_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_funct_1)).
% 4.51/1.84  tff(f_64, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((![B]: ~(r2_hidden(B, k2_relat_1(A)) & (![C]: ~(k10_relat_1(A, k1_tarski(B)) = k1_tarski(C))))) <=> v2_funct_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_funct_1)).
% 4.51/1.84  tff(c_66, plain, (~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.51/1.84  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.51/1.84  tff(c_123, plain, (![A_60, B_61]: (~r2_hidden(A_60, k2_zfmisc_1(A_60, B_61)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.51/1.84  tff(c_129, plain, (![A_1]: (~r2_hidden(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_123])).
% 4.51/1.84  tff(c_78, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.51/1.84  tff(c_141, plain, (![C_64, A_65, B_66]: (v1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.51/1.84  tff(c_158, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_78, c_141])).
% 4.51/1.84  tff(c_82, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.51/1.84  tff(c_228, plain, (![C_76, B_77, A_78]: (v5_relat_1(C_76, B_77) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_78, B_77))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.51/1.84  tff(c_246, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_78, c_228])).
% 4.51/1.84  tff(c_64, plain, (![A_52]: (k6_relat_1(A_52)=k6_partfun1(A_52))), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.51/1.84  tff(c_20, plain, (![A_8]: (v2_funct_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.51/1.84  tff(c_83, plain, (![A_8]: (v2_funct_1(k6_partfun1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_20])).
% 4.51/1.84  tff(c_74, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.51/1.84  tff(c_70, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.51/1.84  tff(c_667, plain, (![E_162, B_159, D_161, C_163, A_164, F_160]: (k1_partfun1(A_164, B_159, C_163, D_161, E_162, F_160)=k5_relat_1(E_162, F_160) | ~m1_subset_1(F_160, k1_zfmisc_1(k2_zfmisc_1(C_163, D_161))) | ~v1_funct_1(F_160) | ~m1_subset_1(E_162, k1_zfmisc_1(k2_zfmisc_1(A_164, B_159))) | ~v1_funct_1(E_162))), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.51/1.84  tff(c_671, plain, (![A_164, B_159, E_162]: (k1_partfun1(A_164, B_159, '#skF_4', '#skF_3', E_162, '#skF_6')=k5_relat_1(E_162, '#skF_6') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_162, k1_zfmisc_1(k2_zfmisc_1(A_164, B_159))) | ~v1_funct_1(E_162))), inference(resolution, [status(thm)], [c_70, c_667])).
% 4.51/1.84  tff(c_886, plain, (![A_184, B_185, E_186]: (k1_partfun1(A_184, B_185, '#skF_4', '#skF_3', E_186, '#skF_6')=k5_relat_1(E_186, '#skF_6') | ~m1_subset_1(E_186, k1_zfmisc_1(k2_zfmisc_1(A_184, B_185))) | ~v1_funct_1(E_186))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_671])).
% 4.51/1.84  tff(c_901, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_78, c_886])).
% 4.51/1.84  tff(c_918, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_901])).
% 4.51/1.84  tff(c_54, plain, (![E_43, F_44, D_42, A_39, C_41, B_40]: (m1_subset_1(k1_partfun1(A_39, B_40, C_41, D_42, E_43, F_44), k1_zfmisc_1(k2_zfmisc_1(A_39, D_42))) | ~m1_subset_1(F_44, k1_zfmisc_1(k2_zfmisc_1(C_41, D_42))) | ~v1_funct_1(F_44) | ~m1_subset_1(E_43, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))) | ~v1_funct_1(E_43))), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.51/1.84  tff(c_1132, plain, (m1_subset_1(k5_relat_1('#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_918, c_54])).
% 4.51/1.84  tff(c_1136, plain, (m1_subset_1(k5_relat_1('#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_74, c_70, c_1132])).
% 4.51/1.84  tff(c_60, plain, (![A_45]: (m1_subset_1(k6_partfun1(A_45), k1_zfmisc_1(k2_zfmisc_1(A_45, A_45))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.51/1.84  tff(c_68, plain, (r2_relset_1('#skF_3', '#skF_3', k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k6_partfun1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.51/1.84  tff(c_540, plain, (![D_137, C_138, A_139, B_140]: (D_137=C_138 | ~r2_relset_1(A_139, B_140, C_138, D_137) | ~m1_subset_1(D_137, k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.51/1.84  tff(c_552, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3') | ~m1_subset_1(k6_partfun1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(resolution, [status(thm)], [c_68, c_540])).
% 4.51/1.84  tff(c_575, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3') | ~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_552])).
% 4.51/1.84  tff(c_1265, plain, (k5_relat_1('#skF_5', '#skF_6')=k6_partfun1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1136, c_918, c_918, c_575])).
% 4.51/1.84  tff(c_12, plain, (![B_6, A_5]: (r1_tarski(k2_relat_1(B_6), A_5) | ~v5_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.51/1.84  tff(c_157, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_70, c_141])).
% 4.51/1.84  tff(c_76, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.51/1.84  tff(c_80, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.51/1.84  tff(c_316, plain, (![A_97, B_98, C_99]: (k1_relset_1(A_97, B_98, C_99)=k1_relat_1(C_99) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.51/1.84  tff(c_334, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_78, c_316])).
% 4.51/1.84  tff(c_431, plain, (![B_123, A_124, C_125]: (k1_xboole_0=B_123 | k1_relset_1(A_124, B_123, C_125)=A_124 | ~v1_funct_2(C_125, A_124, B_123) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(A_124, B_123))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.51/1.84  tff(c_440, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_78, c_431])).
% 4.51/1.84  tff(c_454, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_334, c_440])).
% 4.51/1.84  tff(c_455, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_76, c_454])).
% 4.51/1.84  tff(c_176, plain, (![A_70]: (k2_relat_1(A_70)=k1_xboole_0 | k1_relat_1(A_70)!=k1_xboole_0 | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.51/1.84  tff(c_186, plain, (k2_relat_1('#skF_5')=k1_xboole_0 | k1_relat_1('#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_158, c_176])).
% 4.51/1.84  tff(c_189, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_186])).
% 4.51/1.84  tff(c_458, plain, (k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_455, c_189])).
% 4.51/1.84  tff(c_72, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.51/1.84  tff(c_333, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_70, c_316])).
% 4.51/1.84  tff(c_437, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_4', '#skF_3', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_70, c_431])).
% 4.51/1.84  tff(c_451, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_333, c_437])).
% 4.51/1.84  tff(c_463, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_458, c_451])).
% 4.51/1.84  tff(c_576, plain, (![B_141, A_142]: (v2_funct_1(B_141) | ~r1_tarski(k2_relat_1(B_141), k1_relat_1(A_142)) | ~v2_funct_1(k5_relat_1(B_141, A_142)) | ~v1_funct_1(B_141) | ~v1_relat_1(B_141) | ~v1_funct_1(A_142) | ~v1_relat_1(A_142))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.51/1.84  tff(c_579, plain, (![B_141]: (v2_funct_1(B_141) | ~r1_tarski(k2_relat_1(B_141), '#skF_4') | ~v2_funct_1(k5_relat_1(B_141, '#skF_6')) | ~v1_funct_1(B_141) | ~v1_relat_1(B_141) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_463, c_576])).
% 4.51/1.84  tff(c_627, plain, (![B_151]: (v2_funct_1(B_151) | ~r1_tarski(k2_relat_1(B_151), '#skF_4') | ~v2_funct_1(k5_relat_1(B_151, '#skF_6')) | ~v1_funct_1(B_151) | ~v1_relat_1(B_151))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_74, c_579])).
% 4.51/1.84  tff(c_637, plain, (![B_6]: (v2_funct_1(B_6) | ~v2_funct_1(k5_relat_1(B_6, '#skF_6')) | ~v1_funct_1(B_6) | ~v5_relat_1(B_6, '#skF_4') | ~v1_relat_1(B_6))), inference(resolution, [status(thm)], [c_12, c_627])).
% 4.51/1.84  tff(c_1284, plain, (v2_funct_1('#skF_5') | ~v2_funct_1(k6_partfun1('#skF_3')) | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1265, c_637])).
% 4.51/1.84  tff(c_1288, plain, (v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_158, c_246, c_82, c_83, c_1284])).
% 4.51/1.84  tff(c_1290, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_1288])).
% 4.51/1.84  tff(c_1291, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_186])).
% 4.51/1.84  tff(c_1419, plain, (![A_213]: (r2_hidden('#skF_1'(A_213), k2_relat_1(A_213)) | v2_funct_1(A_213) | ~v1_funct_1(A_213) | ~v1_relat_1(A_213))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.51/1.84  tff(c_1425, plain, (r2_hidden('#skF_1'('#skF_5'), k1_xboole_0) | v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1291, c_1419])).
% 4.51/1.84  tff(c_1430, plain, (r2_hidden('#skF_1'('#skF_5'), k1_xboole_0) | v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_158, c_82, c_1425])).
% 4.51/1.84  tff(c_1432, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_129, c_1430])).
% 4.51/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.51/1.84  
% 4.51/1.84  Inference rules
% 4.51/1.84  ----------------------
% 4.51/1.84  #Ref     : 0
% 4.51/1.84  #Sup     : 292
% 4.51/1.85  #Fact    : 0
% 4.51/1.85  #Define  : 0
% 4.51/1.85  #Split   : 8
% 4.51/1.85  #Chain   : 0
% 4.51/1.85  #Close   : 0
% 4.51/1.85  
% 4.51/1.85  Ordering : KBO
% 4.51/1.85  
% 4.51/1.85  Simplification rules
% 4.51/1.85  ----------------------
% 4.51/1.85  #Subsume      : 18
% 4.51/1.85  #Demod        : 166
% 4.51/1.85  #Tautology    : 91
% 4.51/1.85  #SimpNegUnit  : 21
% 4.51/1.85  #BackRed      : 18
% 4.51/1.85  
% 4.51/1.85  #Partial instantiations: 0
% 4.51/1.85  #Strategies tried      : 1
% 4.51/1.85  
% 4.51/1.85  Timing (in seconds)
% 4.51/1.85  ----------------------
% 4.51/1.85  Preprocessing        : 0.42
% 4.51/1.85  Parsing              : 0.24
% 4.51/1.85  CNF conversion       : 0.03
% 4.51/1.85  Main loop            : 0.58
% 4.51/1.85  Inferencing          : 0.21
% 4.51/1.85  Reduction            : 0.19
% 4.51/1.85  Demodulation         : 0.14
% 4.51/1.85  BG Simplification    : 0.03
% 4.51/1.85  Subsumption          : 0.10
% 4.51/1.85  Abstraction          : 0.02
% 4.51/1.85  MUC search           : 0.00
% 4.51/1.85  Cooper               : 0.00
% 4.51/1.85  Total                : 1.06
% 4.51/1.85  Index Insertion      : 0.00
% 4.51/1.85  Index Deletion       : 0.00
% 4.51/1.85  Index Matching       : 0.00
% 4.51/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
