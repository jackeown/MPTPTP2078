%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:57 EST 2020

% Result     : Theorem 3.86s
% Output     : CNFRefutation 4.10s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 736 expanded)
%              Number of leaves         :   44 ( 279 expanded)
%              Depth                    :   19
%              Number of atoms          :  241 (2497 expanded)
%              Number of equality atoms :   73 ( 648 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(f_161,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ( ( v1_funct_1(E)
              & v1_funct_2(E,B,C)
              & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
           => ( ( k2_relset_1(A,C,k1_partfun1(A,B,B,C,D,E)) = C
                & v2_funct_1(E) )
             => ( C = k1_xboole_0
                | k2_relset_1(A,B,D) = B ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_funct_2)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_139,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_129,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_81,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v2_funct_1(A)
            & r1_tarski(B,k1_relat_1(A)) )
         => k9_relat_1(k2_funct_1(A),k9_relat_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t177_funct_1)).

tff(c_68,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_119,plain,(
    ! [C_59,B_60,A_61] :
      ( v5_relat_1(C_59,B_60)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_61,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_126,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_119])).

tff(c_75,plain,(
    ! [C_49,A_50,B_51] :
      ( v1_relat_1(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_82,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_75])).

tff(c_157,plain,(
    ! [C_69,A_70,B_71] :
      ( v4_relat_1(C_69,A_70)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_164,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_157])).

tff(c_20,plain,(
    ! [B_14,A_13] :
      ( k7_relat_1(B_14,A_13) = B_14
      | ~ v4_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_168,plain,
    ( k7_relat_1('#skF_4','#skF_1') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_164,c_20])).

tff(c_171,plain,(
    k7_relat_1('#skF_4','#skF_1') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_168])).

tff(c_14,plain,(
    ! [B_8,A_7] :
      ( k2_relat_1(k7_relat_1(B_8,A_7)) = k9_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_181,plain,
    ( k9_relat_1('#skF_4','#skF_1') = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_14])).

tff(c_185,plain,(
    k9_relat_1('#skF_4','#skF_1') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_181])).

tff(c_146,plain,(
    ! [B_67,A_68] :
      ( r1_tarski(k2_relat_1(B_67),A_68)
      | ~ v5_relat_1(B_67,A_68)
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_800,plain,(
    ! [B_148,A_149,A_150] :
      ( r1_tarski(k9_relat_1(B_148,A_149),A_150)
      | ~ v5_relat_1(k7_relat_1(B_148,A_149),A_150)
      | ~ v1_relat_1(k7_relat_1(B_148,A_149))
      | ~ v1_relat_1(B_148) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_146])).

tff(c_809,plain,(
    ! [A_150] :
      ( r1_tarski(k9_relat_1('#skF_4','#skF_1'),A_150)
      | ~ v5_relat_1('#skF_4',A_150)
      | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_1'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_800])).

tff(c_819,plain,(
    ! [A_150] :
      ( r1_tarski(k2_relat_1('#skF_4'),A_150)
      | ~ v5_relat_1('#skF_4',A_150) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_82,c_171,c_185,c_809])).

tff(c_214,plain,(
    ! [A_72,B_73,C_74] :
      ( k2_relset_1(A_72,B_73,C_74) = k2_relat_1(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_221,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_214])).

tff(c_54,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_223,plain,(
    k2_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_54])).

tff(c_62,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_83,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_75])).

tff(c_66,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_58,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_64,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_228,plain,(
    ! [A_75,B_76,C_77] :
      ( k1_relset_1(A_75,B_76,C_77) = k1_relat_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_236,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_228])).

tff(c_541,plain,(
    ! [B_113,A_114,C_115] :
      ( k1_xboole_0 = B_113
      | k1_relset_1(A_114,B_113,C_115) = A_114
      | ~ v1_funct_2(C_115,A_114,B_113)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_114,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_547,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_541])).

tff(c_553,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_236,c_547])).

tff(c_554,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_553])).

tff(c_127,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_119])).

tff(c_72,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_747,plain,(
    ! [C_136,D_137,F_138,E_134,B_139,A_135] :
      ( k1_partfun1(A_135,B_139,C_136,D_137,E_134,F_138) = k5_relat_1(E_134,F_138)
      | ~ m1_subset_1(F_138,k1_zfmisc_1(k2_zfmisc_1(C_136,D_137)))
      | ~ v1_funct_1(F_138)
      | ~ m1_subset_1(E_134,k1_zfmisc_1(k2_zfmisc_1(A_135,B_139)))
      | ~ v1_funct_1(E_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_751,plain,(
    ! [A_135,B_139,E_134] :
      ( k1_partfun1(A_135,B_139,'#skF_2','#skF_3',E_134,'#skF_5') = k5_relat_1(E_134,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_134,k1_zfmisc_1(k2_zfmisc_1(A_135,B_139)))
      | ~ v1_funct_1(E_134) ) ),
    inference(resolution,[status(thm)],[c_62,c_747])).

tff(c_996,plain,(
    ! [A_160,B_161,E_162] :
      ( k1_partfun1(A_160,B_161,'#skF_2','#skF_3',E_162,'#skF_5') = k5_relat_1(E_162,'#skF_5')
      | ~ m1_subset_1(E_162,k1_zfmisc_1(k2_zfmisc_1(A_160,B_161)))
      | ~ v1_funct_1(E_162) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_751])).

tff(c_1002,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_996])).

tff(c_1009,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1002])).

tff(c_60,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_1014,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1009,c_60])).

tff(c_48,plain,(
    ! [A_35,F_40,B_36,C_37,D_38,E_39] :
      ( m1_subset_1(k1_partfun1(A_35,B_36,C_37,D_38,E_39,F_40),k1_zfmisc_1(k2_zfmisc_1(A_35,D_38)))
      | ~ m1_subset_1(F_40,k1_zfmisc_1(k2_zfmisc_1(C_37,D_38)))
      | ~ v1_funct_1(F_40)
      | ~ m1_subset_1(E_39,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36)))
      | ~ v1_funct_1(E_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1018,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1009,c_48])).

tff(c_1022,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_66,c_62,c_1018])).

tff(c_34,plain,(
    ! [A_29,B_30,C_31] :
      ( k2_relset_1(A_29,B_30,C_31) = k2_relat_1(C_31)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1052,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_1022,c_34])).

tff(c_1085,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1014,c_1052])).

tff(c_16,plain,(
    ! [B_11,A_9] :
      ( k9_relat_1(B_11,k2_relat_1(A_9)) = k2_relat_1(k5_relat_1(A_9,B_11))
      | ~ v1_relat_1(B_11)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_165,plain,(
    v4_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_157])).

tff(c_174,plain,
    ( k7_relat_1('#skF_5','#skF_2') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_165,c_20])).

tff(c_177,plain,(
    k7_relat_1('#skF_5','#skF_2') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_174])).

tff(c_190,plain,
    ( k9_relat_1('#skF_5','#skF_2') = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_14])).

tff(c_194,plain,(
    k9_relat_1('#skF_5','#skF_2') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_190])).

tff(c_104,plain,(
    ! [B_57,A_58] :
      ( k2_relat_1(k7_relat_1(B_57,A_58)) = k9_relat_1(B_57,A_58)
      | ~ v1_relat_1(B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12,plain,(
    ! [B_6,A_5] :
      ( r1_tarski(k9_relat_1(B_6,A_5),k2_relat_1(B_6))
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_409,plain,(
    ! [B_104,A_105,A_106] :
      ( r1_tarski(k9_relat_1(k7_relat_1(B_104,A_105),A_106),k9_relat_1(B_104,A_105))
      | ~ v1_relat_1(k7_relat_1(B_104,A_105))
      | ~ v1_relat_1(B_104) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_12])).

tff(c_430,plain,(
    ! [A_106] :
      ( r1_tarski(k9_relat_1('#skF_5',A_106),k9_relat_1('#skF_5','#skF_2'))
      | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_2'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_409])).

tff(c_443,plain,(
    ! [A_107] : r1_tarski(k9_relat_1('#skF_5',A_107),k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_83,c_177,c_194,c_430])).

tff(c_452,plain,(
    ! [A_9] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_9,'#skF_5')),k2_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5')
      | ~ v1_relat_1(A_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_443])).

tff(c_515,plain,(
    ! [A_111] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_111,'#skF_5')),k2_relat_1('#skF_5'))
      | ~ v1_relat_1(A_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_452])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_156,plain,(
    ! [B_67,A_68] :
      ( k2_relat_1(B_67) = A_68
      | ~ r1_tarski(A_68,k2_relat_1(B_67))
      | ~ v5_relat_1(B_67,A_68)
      | ~ v1_relat_1(B_67) ) ),
    inference(resolution,[status(thm)],[c_146,c_2])).

tff(c_518,plain,(
    ! [A_111] :
      ( k2_relat_1(k5_relat_1(A_111,'#skF_5')) = k2_relat_1('#skF_5')
      | ~ v5_relat_1('#skF_5',k2_relat_1(k5_relat_1(A_111,'#skF_5')))
      | ~ v1_relat_1('#skF_5')
      | ~ v1_relat_1(A_111) ) ),
    inference(resolution,[status(thm)],[c_515,c_156])).

tff(c_526,plain,(
    ! [A_111] :
      ( k2_relat_1(k5_relat_1(A_111,'#skF_5')) = k2_relat_1('#skF_5')
      | ~ v5_relat_1('#skF_5',k2_relat_1(k5_relat_1(A_111,'#skF_5')))
      | ~ v1_relat_1(A_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_518])).

tff(c_1121,plain,
    ( k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = k2_relat_1('#skF_5')
    | ~ v5_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1085,c_526])).

tff(c_1167,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_127,c_1085,c_1121])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_605,plain,(
    ! [A_119,B_120] :
      ( k9_relat_1(k2_funct_1(A_119),k9_relat_1(A_119,B_120)) = B_120
      | ~ r1_tarski(B_120,k1_relat_1(A_119))
      | ~ v2_funct_1(A_119)
      | ~ v1_funct_1(A_119)
      | ~ v1_relat_1(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_648,plain,
    ( k9_relat_1(k2_funct_1('#skF_5'),k2_relat_1('#skF_5')) = '#skF_2'
    | ~ r1_tarski('#skF_2',k1_relat_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_605])).

tff(c_655,plain,(
    k9_relat_1(k2_funct_1('#skF_5'),k2_relat_1('#skF_5')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_66,c_58,c_6,c_554,c_648])).

tff(c_1201,plain,(
    k9_relat_1(k2_funct_1('#skF_5'),'#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1167,c_655])).

tff(c_446,plain,(
    ! [A_107] :
      ( k9_relat_1('#skF_5',A_107) = k2_relat_1('#skF_5')
      | ~ v5_relat_1('#skF_5',k9_relat_1('#skF_5',A_107))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_443,c_156])).

tff(c_529,plain,(
    ! [A_112] :
      ( k9_relat_1('#skF_5',A_112) = k2_relat_1('#skF_5')
      | ~ v5_relat_1('#skF_5',k9_relat_1('#skF_5',A_112)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_446])).

tff(c_533,plain,(
    ! [A_9] :
      ( k9_relat_1('#skF_5',k2_relat_1(A_9)) = k2_relat_1('#skF_5')
      | ~ v5_relat_1('#skF_5',k2_relat_1(k5_relat_1(A_9,'#skF_5')))
      | ~ v1_relat_1('#skF_5')
      | ~ v1_relat_1(A_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_529])).

tff(c_538,plain,(
    ! [A_9] :
      ( k9_relat_1('#skF_5',k2_relat_1(A_9)) = k2_relat_1('#skF_5')
      | ~ v5_relat_1('#skF_5',k2_relat_1(k5_relat_1(A_9,'#skF_5')))
      | ~ v1_relat_1(A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_533])).

tff(c_1118,plain,
    ( k9_relat_1('#skF_5',k2_relat_1('#skF_4')) = k2_relat_1('#skF_5')
    | ~ v5_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1085,c_538])).

tff(c_1165,plain,(
    k9_relat_1('#skF_5',k2_relat_1('#skF_4')) = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_127,c_1118])).

tff(c_1461,plain,(
    k9_relat_1('#skF_5',k2_relat_1('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1167,c_1165])).

tff(c_24,plain,(
    ! [A_17,B_19] :
      ( k9_relat_1(k2_funct_1(A_17),k9_relat_1(A_17,B_19)) = B_19
      | ~ r1_tarski(B_19,k1_relat_1(A_17))
      | ~ v2_funct_1(A_17)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1470,plain,
    ( k9_relat_1(k2_funct_1('#skF_5'),'#skF_3') = k2_relat_1('#skF_4')
    | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relat_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1461,c_24])).

tff(c_1498,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_66,c_58,c_554,c_1201,c_1470])).

tff(c_1499,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_223,c_1498])).

tff(c_1517,plain,(
    ~ v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_819,c_1499])).

tff(c_1524,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_1517])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:26:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.86/1.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.86/1.66  
% 3.86/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.86/1.66  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.86/1.66  
% 3.86/1.66  %Foreground sorts:
% 3.86/1.66  
% 3.86/1.66  
% 3.86/1.66  %Background operators:
% 3.86/1.66  
% 3.86/1.66  
% 3.86/1.66  %Foreground operators:
% 3.86/1.66  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.86/1.66  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.86/1.66  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.86/1.66  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.86/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.86/1.66  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.86/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.86/1.66  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.86/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.86/1.66  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.86/1.66  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.86/1.66  tff('#skF_5', type, '#skF_5': $i).
% 3.86/1.66  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.86/1.66  tff('#skF_2', type, '#skF_2': $i).
% 3.86/1.66  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.86/1.66  tff('#skF_3', type, '#skF_3': $i).
% 3.86/1.66  tff('#skF_1', type, '#skF_1': $i).
% 3.86/1.66  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.86/1.66  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.86/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.86/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.86/1.66  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.86/1.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.86/1.66  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.86/1.66  tff('#skF_4', type, '#skF_4': $i).
% 3.86/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.86/1.66  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.86/1.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.86/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.86/1.66  
% 4.10/1.69  tff(f_161, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C) & v2_funct_1(E)) => ((C = k1_xboole_0) | (k2_relset_1(A, B, D) = B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_funct_2)).
% 4.10/1.69  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.10/1.69  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.10/1.69  tff(f_62, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 4.10/1.69  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 4.10/1.69  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 4.10/1.69  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.10/1.69  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.10/1.69  tff(f_117, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.10/1.69  tff(f_139, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 4.10/1.69  tff(f_129, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 4.10/1.69  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 4.10/1.69  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 4.10/1.69  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.10/1.69  tff(f_81, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v2_funct_1(A) & r1_tarski(B, k1_relat_1(A))) => (k9_relat_1(k2_funct_1(A), k9_relat_1(A, B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t177_funct_1)).
% 4.10/1.69  tff(c_68, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.10/1.69  tff(c_119, plain, (![C_59, B_60, A_61]: (v5_relat_1(C_59, B_60) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_61, B_60))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.10/1.69  tff(c_126, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_68, c_119])).
% 4.10/1.69  tff(c_75, plain, (![C_49, A_50, B_51]: (v1_relat_1(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.10/1.69  tff(c_82, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_75])).
% 4.10/1.69  tff(c_157, plain, (![C_69, A_70, B_71]: (v4_relat_1(C_69, A_70) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.10/1.69  tff(c_164, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_68, c_157])).
% 4.10/1.69  tff(c_20, plain, (![B_14, A_13]: (k7_relat_1(B_14, A_13)=B_14 | ~v4_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.10/1.69  tff(c_168, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_164, c_20])).
% 4.10/1.69  tff(c_171, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_168])).
% 4.10/1.69  tff(c_14, plain, (![B_8, A_7]: (k2_relat_1(k7_relat_1(B_8, A_7))=k9_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.10/1.69  tff(c_181, plain, (k9_relat_1('#skF_4', '#skF_1')=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_171, c_14])).
% 4.10/1.69  tff(c_185, plain, (k9_relat_1('#skF_4', '#skF_1')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_181])).
% 4.10/1.69  tff(c_146, plain, (![B_67, A_68]: (r1_tarski(k2_relat_1(B_67), A_68) | ~v5_relat_1(B_67, A_68) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.10/1.69  tff(c_800, plain, (![B_148, A_149, A_150]: (r1_tarski(k9_relat_1(B_148, A_149), A_150) | ~v5_relat_1(k7_relat_1(B_148, A_149), A_150) | ~v1_relat_1(k7_relat_1(B_148, A_149)) | ~v1_relat_1(B_148))), inference(superposition, [status(thm), theory('equality')], [c_14, c_146])).
% 4.10/1.69  tff(c_809, plain, (![A_150]: (r1_tarski(k9_relat_1('#skF_4', '#skF_1'), A_150) | ~v5_relat_1('#skF_4', A_150) | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_1')) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_171, c_800])).
% 4.10/1.69  tff(c_819, plain, (![A_150]: (r1_tarski(k2_relat_1('#skF_4'), A_150) | ~v5_relat_1('#skF_4', A_150))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_82, c_171, c_185, c_809])).
% 4.10/1.69  tff(c_214, plain, (![A_72, B_73, C_74]: (k2_relset_1(A_72, B_73, C_74)=k2_relat_1(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.10/1.69  tff(c_221, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_214])).
% 4.10/1.69  tff(c_54, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.10/1.69  tff(c_223, plain, (k2_relat_1('#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_221, c_54])).
% 4.10/1.69  tff(c_62, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.10/1.69  tff(c_83, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_75])).
% 4.10/1.69  tff(c_66, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.10/1.69  tff(c_58, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.10/1.69  tff(c_56, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.10/1.69  tff(c_64, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.10/1.69  tff(c_228, plain, (![A_75, B_76, C_77]: (k1_relset_1(A_75, B_76, C_77)=k1_relat_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.10/1.69  tff(c_236, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_228])).
% 4.10/1.69  tff(c_541, plain, (![B_113, A_114, C_115]: (k1_xboole_0=B_113 | k1_relset_1(A_114, B_113, C_115)=A_114 | ~v1_funct_2(C_115, A_114, B_113) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_114, B_113))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.10/1.69  tff(c_547, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_62, c_541])).
% 4.10/1.69  tff(c_553, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_236, c_547])).
% 4.10/1.69  tff(c_554, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_56, c_553])).
% 4.10/1.69  tff(c_127, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_62, c_119])).
% 4.10/1.69  tff(c_72, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.10/1.69  tff(c_747, plain, (![C_136, D_137, F_138, E_134, B_139, A_135]: (k1_partfun1(A_135, B_139, C_136, D_137, E_134, F_138)=k5_relat_1(E_134, F_138) | ~m1_subset_1(F_138, k1_zfmisc_1(k2_zfmisc_1(C_136, D_137))) | ~v1_funct_1(F_138) | ~m1_subset_1(E_134, k1_zfmisc_1(k2_zfmisc_1(A_135, B_139))) | ~v1_funct_1(E_134))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.10/1.69  tff(c_751, plain, (![A_135, B_139, E_134]: (k1_partfun1(A_135, B_139, '#skF_2', '#skF_3', E_134, '#skF_5')=k5_relat_1(E_134, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_134, k1_zfmisc_1(k2_zfmisc_1(A_135, B_139))) | ~v1_funct_1(E_134))), inference(resolution, [status(thm)], [c_62, c_747])).
% 4.10/1.69  tff(c_996, plain, (![A_160, B_161, E_162]: (k1_partfun1(A_160, B_161, '#skF_2', '#skF_3', E_162, '#skF_5')=k5_relat_1(E_162, '#skF_5') | ~m1_subset_1(E_162, k1_zfmisc_1(k2_zfmisc_1(A_160, B_161))) | ~v1_funct_1(E_162))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_751])).
% 4.10/1.69  tff(c_1002, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_996])).
% 4.10/1.69  tff(c_1009, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1002])).
% 4.10/1.69  tff(c_60, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.10/1.69  tff(c_1014, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1009, c_60])).
% 4.10/1.69  tff(c_48, plain, (![A_35, F_40, B_36, C_37, D_38, E_39]: (m1_subset_1(k1_partfun1(A_35, B_36, C_37, D_38, E_39, F_40), k1_zfmisc_1(k2_zfmisc_1(A_35, D_38))) | ~m1_subset_1(F_40, k1_zfmisc_1(k2_zfmisc_1(C_37, D_38))) | ~v1_funct_1(F_40) | ~m1_subset_1(E_39, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))) | ~v1_funct_1(E_39))), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.10/1.69  tff(c_1018, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1009, c_48])).
% 4.10/1.69  tff(c_1022, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_66, c_62, c_1018])).
% 4.10/1.69  tff(c_34, plain, (![A_29, B_30, C_31]: (k2_relset_1(A_29, B_30, C_31)=k2_relat_1(C_31) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.10/1.69  tff(c_1052, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_1022, c_34])).
% 4.10/1.69  tff(c_1085, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1014, c_1052])).
% 4.10/1.69  tff(c_16, plain, (![B_11, A_9]: (k9_relat_1(B_11, k2_relat_1(A_9))=k2_relat_1(k5_relat_1(A_9, B_11)) | ~v1_relat_1(B_11) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.10/1.69  tff(c_165, plain, (v4_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_62, c_157])).
% 4.10/1.69  tff(c_174, plain, (k7_relat_1('#skF_5', '#skF_2')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_165, c_20])).
% 4.10/1.69  tff(c_177, plain, (k7_relat_1('#skF_5', '#skF_2')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_83, c_174])).
% 4.10/1.69  tff(c_190, plain, (k9_relat_1('#skF_5', '#skF_2')=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_177, c_14])).
% 4.10/1.69  tff(c_194, plain, (k9_relat_1('#skF_5', '#skF_2')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_190])).
% 4.10/1.69  tff(c_104, plain, (![B_57, A_58]: (k2_relat_1(k7_relat_1(B_57, A_58))=k9_relat_1(B_57, A_58) | ~v1_relat_1(B_57))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.10/1.69  tff(c_12, plain, (![B_6, A_5]: (r1_tarski(k9_relat_1(B_6, A_5), k2_relat_1(B_6)) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.10/1.69  tff(c_409, plain, (![B_104, A_105, A_106]: (r1_tarski(k9_relat_1(k7_relat_1(B_104, A_105), A_106), k9_relat_1(B_104, A_105)) | ~v1_relat_1(k7_relat_1(B_104, A_105)) | ~v1_relat_1(B_104))), inference(superposition, [status(thm), theory('equality')], [c_104, c_12])).
% 4.10/1.69  tff(c_430, plain, (![A_106]: (r1_tarski(k9_relat_1('#skF_5', A_106), k9_relat_1('#skF_5', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_2')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_177, c_409])).
% 4.10/1.69  tff(c_443, plain, (![A_107]: (r1_tarski(k9_relat_1('#skF_5', A_107), k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_83, c_177, c_194, c_430])).
% 4.10/1.69  tff(c_452, plain, (![A_9]: (r1_tarski(k2_relat_1(k5_relat_1(A_9, '#skF_5')), k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5') | ~v1_relat_1(A_9))), inference(superposition, [status(thm), theory('equality')], [c_16, c_443])).
% 4.10/1.69  tff(c_515, plain, (![A_111]: (r1_tarski(k2_relat_1(k5_relat_1(A_111, '#skF_5')), k2_relat_1('#skF_5')) | ~v1_relat_1(A_111))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_452])).
% 4.10/1.69  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.10/1.69  tff(c_156, plain, (![B_67, A_68]: (k2_relat_1(B_67)=A_68 | ~r1_tarski(A_68, k2_relat_1(B_67)) | ~v5_relat_1(B_67, A_68) | ~v1_relat_1(B_67))), inference(resolution, [status(thm)], [c_146, c_2])).
% 4.10/1.69  tff(c_518, plain, (![A_111]: (k2_relat_1(k5_relat_1(A_111, '#skF_5'))=k2_relat_1('#skF_5') | ~v5_relat_1('#skF_5', k2_relat_1(k5_relat_1(A_111, '#skF_5'))) | ~v1_relat_1('#skF_5') | ~v1_relat_1(A_111))), inference(resolution, [status(thm)], [c_515, c_156])).
% 4.10/1.69  tff(c_526, plain, (![A_111]: (k2_relat_1(k5_relat_1(A_111, '#skF_5'))=k2_relat_1('#skF_5') | ~v5_relat_1('#skF_5', k2_relat_1(k5_relat_1(A_111, '#skF_5'))) | ~v1_relat_1(A_111))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_518])).
% 4.10/1.69  tff(c_1121, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1('#skF_5') | ~v5_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1085, c_526])).
% 4.10/1.69  tff(c_1167, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_127, c_1085, c_1121])).
% 4.10/1.69  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.10/1.69  tff(c_605, plain, (![A_119, B_120]: (k9_relat_1(k2_funct_1(A_119), k9_relat_1(A_119, B_120))=B_120 | ~r1_tarski(B_120, k1_relat_1(A_119)) | ~v2_funct_1(A_119) | ~v1_funct_1(A_119) | ~v1_relat_1(A_119))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.10/1.69  tff(c_648, plain, (k9_relat_1(k2_funct_1('#skF_5'), k2_relat_1('#skF_5'))='#skF_2' | ~r1_tarski('#skF_2', k1_relat_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_194, c_605])).
% 4.10/1.69  tff(c_655, plain, (k9_relat_1(k2_funct_1('#skF_5'), k2_relat_1('#skF_5'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_83, c_66, c_58, c_6, c_554, c_648])).
% 4.10/1.69  tff(c_1201, plain, (k9_relat_1(k2_funct_1('#skF_5'), '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1167, c_655])).
% 4.10/1.69  tff(c_446, plain, (![A_107]: (k9_relat_1('#skF_5', A_107)=k2_relat_1('#skF_5') | ~v5_relat_1('#skF_5', k9_relat_1('#skF_5', A_107)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_443, c_156])).
% 4.10/1.69  tff(c_529, plain, (![A_112]: (k9_relat_1('#skF_5', A_112)=k2_relat_1('#skF_5') | ~v5_relat_1('#skF_5', k9_relat_1('#skF_5', A_112)))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_446])).
% 4.10/1.69  tff(c_533, plain, (![A_9]: (k9_relat_1('#skF_5', k2_relat_1(A_9))=k2_relat_1('#skF_5') | ~v5_relat_1('#skF_5', k2_relat_1(k5_relat_1(A_9, '#skF_5'))) | ~v1_relat_1('#skF_5') | ~v1_relat_1(A_9))), inference(superposition, [status(thm), theory('equality')], [c_16, c_529])).
% 4.10/1.69  tff(c_538, plain, (![A_9]: (k9_relat_1('#skF_5', k2_relat_1(A_9))=k2_relat_1('#skF_5') | ~v5_relat_1('#skF_5', k2_relat_1(k5_relat_1(A_9, '#skF_5'))) | ~v1_relat_1(A_9))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_533])).
% 4.10/1.69  tff(c_1118, plain, (k9_relat_1('#skF_5', k2_relat_1('#skF_4'))=k2_relat_1('#skF_5') | ~v5_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1085, c_538])).
% 4.10/1.69  tff(c_1165, plain, (k9_relat_1('#skF_5', k2_relat_1('#skF_4'))=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_127, c_1118])).
% 4.10/1.69  tff(c_1461, plain, (k9_relat_1('#skF_5', k2_relat_1('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1167, c_1165])).
% 4.10/1.69  tff(c_24, plain, (![A_17, B_19]: (k9_relat_1(k2_funct_1(A_17), k9_relat_1(A_17, B_19))=B_19 | ~r1_tarski(B_19, k1_relat_1(A_17)) | ~v2_funct_1(A_17) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.10/1.69  tff(c_1470, plain, (k9_relat_1(k2_funct_1('#skF_5'), '#skF_3')=k2_relat_1('#skF_4') | ~r1_tarski(k2_relat_1('#skF_4'), k1_relat_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1461, c_24])).
% 4.10/1.69  tff(c_1498, plain, (k2_relat_1('#skF_4')='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_66, c_58, c_554, c_1201, c_1470])).
% 4.10/1.69  tff(c_1499, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_223, c_1498])).
% 4.10/1.69  tff(c_1517, plain, (~v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_819, c_1499])).
% 4.10/1.69  tff(c_1524, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_126, c_1517])).
% 4.10/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.10/1.69  
% 4.10/1.69  Inference rules
% 4.10/1.69  ----------------------
% 4.10/1.69  #Ref     : 0
% 4.10/1.69  #Sup     : 325
% 4.10/1.69  #Fact    : 0
% 4.10/1.69  #Define  : 0
% 4.10/1.69  #Split   : 5
% 4.10/1.69  #Chain   : 0
% 4.10/1.69  #Close   : 0
% 4.10/1.69  
% 4.10/1.69  Ordering : KBO
% 4.10/1.69  
% 4.10/1.69  Simplification rules
% 4.10/1.69  ----------------------
% 4.10/1.69  #Subsume      : 32
% 4.10/1.69  #Demod        : 342
% 4.10/1.69  #Tautology    : 122
% 4.10/1.69  #SimpNegUnit  : 5
% 4.10/1.69  #BackRed      : 21
% 4.10/1.69  
% 4.10/1.69  #Partial instantiations: 0
% 4.10/1.69  #Strategies tried      : 1
% 4.10/1.69  
% 4.10/1.69  Timing (in seconds)
% 4.10/1.69  ----------------------
% 4.10/1.69  Preprocessing        : 0.38
% 4.10/1.69  Parsing              : 0.20
% 4.10/1.69  CNF conversion       : 0.03
% 4.10/1.69  Main loop            : 0.52
% 4.10/1.69  Inferencing          : 0.18
% 4.10/1.69  Reduction            : 0.18
% 4.10/1.69  Demodulation         : 0.13
% 4.10/1.69  BG Simplification    : 0.03
% 4.10/1.69  Subsumption          : 0.09
% 4.10/1.69  Abstraction          : 0.02
% 4.10/1.69  MUC search           : 0.00
% 4.10/1.69  Cooper               : 0.00
% 4.10/1.69  Total                : 0.95
% 4.10/1.69  Index Insertion      : 0.00
% 4.10/1.69  Index Deletion       : 0.00
% 4.10/1.69  Index Matching       : 0.00
% 4.10/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
