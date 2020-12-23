%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0973+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:10 EST 2020

% Result     : Theorem 26.56s
% Output     : CNFRefutation 27.08s
% Verified   : 
% Statistics : Number of formulae       :  500 (6789 expanded)
%              Number of leaves         :   48 (2056 expanded)
%              Depth                    :   26
%              Number of atoms          :  796 (18092 expanded)
%              Number of equality atoms :  261 (6501 expanded)
%              Maximal formula depth    :   14 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k4_relset_1,type,(
    k4_relset_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_157,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ( ( v1_funct_2(E,B,C)
              & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
           => ( ~ ( B = k1_xboole_0
                  & C != k1_xboole_0
                  & A != k1_xboole_0 )
             => v1_funct_2(k4_relset_1(A,B,B,C,D,E),A,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_funct_2)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_71,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_104,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_98,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_53,axiom,(
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

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_108,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_117,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_68,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_128,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_84,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C)
      & v1_funct_2(C,A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).

tff(f_136,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_124,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(c_64,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_31407,plain,(
    ! [C_4229,B_4230,A_4231] :
      ( v1_xboole_0(C_4229)
      | ~ m1_subset_1(C_4229,k1_zfmisc_1(k2_zfmisc_1(B_4230,A_4231)))
      | ~ v1_xboole_0(A_4231) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_31428,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_31407])).

tff(c_31437,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_31428])).

tff(c_26,plain,(
    ! [A_23] : m1_subset_1('#skF_1'(A_23),A_23) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_46,plain,(
    ! [A_40,B_41] :
      ( r2_hidden(A_40,B_41)
      | v1_xboole_0(B_41)
      | ~ m1_subset_1(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_190,plain,(
    ! [C_90,B_91,A_92] :
      ( v1_xboole_0(C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(B_91,A_92)))
      | ~ v1_xboole_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_211,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_190])).

tff(c_214,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_211])).

tff(c_68,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_1188,plain,(
    ! [B_172,F_170,D_169,C_173,E_171,A_168] :
      ( k4_relset_1(A_168,B_172,C_173,D_169,E_171,F_170) = k5_relat_1(E_171,F_170)
      | ~ m1_subset_1(F_170,k1_zfmisc_1(k2_zfmisc_1(C_173,D_169)))
      | ~ m1_subset_1(E_171,k1_zfmisc_1(k2_zfmisc_1(A_168,B_172))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2377,plain,(
    ! [A_1962,B_1963,E_1964] :
      ( k4_relset_1(A_1962,B_1963,'#skF_4','#skF_5',E_1964,'#skF_7') = k5_relat_1(E_1964,'#skF_7')
      | ~ m1_subset_1(E_1964,k1_zfmisc_1(k2_zfmisc_1(A_1962,B_1963))) ) ),
    inference(resolution,[status(thm)],[c_64,c_1188])).

tff(c_2429,plain,(
    k4_relset_1('#skF_3','#skF_4','#skF_4','#skF_5','#skF_6','#skF_7') = k5_relat_1('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_2377])).

tff(c_22,plain,(
    ! [E_21,D_20,C_19,B_18,A_17,F_22] :
      ( m1_subset_1(k4_relset_1(A_17,B_18,C_19,D_20,E_21,F_22),k1_zfmisc_1(k2_zfmisc_1(A_17,D_20)))
      | ~ m1_subset_1(F_22,k1_zfmisc_1(k2_zfmisc_1(C_19,D_20)))
      | ~ m1_subset_1(E_21,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2855,plain,
    ( m1_subset_1(k5_relat_1('#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_5')))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2429,c_22])).

tff(c_2859,plain,(
    m1_subset_1(k5_relat_1('#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_2855])).

tff(c_40,plain,(
    ! [A_28,B_29,C_30] :
      ( k1_relset_1(A_28,B_29,C_30) = k1_relat_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2899,plain,(
    k1_relset_1('#skF_3','#skF_5',k5_relat_1('#skF_6','#skF_7')) = k1_relat_1(k5_relat_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_2859,c_40])).

tff(c_60,plain,(
    ~ v1_funct_2(k4_relset_1('#skF_3','#skF_4','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_2851,plain,(
    ~ v1_funct_2(k5_relat_1('#skF_6','#skF_7'),'#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2429,c_60])).

tff(c_12,plain,(
    ! [B_9,C_10,A_8] :
      ( k1_xboole_0 = B_9
      | v1_funct_2(C_10,A_8,B_9)
      | k1_relset_1(A_8,B_9,C_10) != A_8
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2871,plain,
    ( k1_xboole_0 = '#skF_5'
    | v1_funct_2(k5_relat_1('#skF_6','#skF_7'),'#skF_3','#skF_5')
    | k1_relset_1('#skF_3','#skF_5',k5_relat_1('#skF_6','#skF_7')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_2859,c_12])).

tff(c_2897,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_3','#skF_5',k5_relat_1('#skF_6','#skF_7')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_2851,c_2871])).

tff(c_3214,plain,(
    k1_relset_1('#skF_3','#skF_5',k5_relat_1('#skF_6','#skF_7')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2897])).

tff(c_8593,plain,(
    k1_relat_1(k5_relat_1('#skF_6','#skF_7')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2899,c_3214])).

tff(c_117,plain,(
    ! [C_73,A_74,B_75] :
      ( v1_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_133,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_117])).

tff(c_62,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_89,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_70,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_347,plain,(
    ! [A_109,B_110,C_111] :
      ( k1_relset_1(A_109,B_110,C_111) = k1_relat_1(C_111)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_371,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_347])).

tff(c_924,plain,(
    ! [B_148,A_149,C_150] :
      ( k1_xboole_0 = B_148
      | k1_relset_1(A_149,B_148,C_150) = A_149
      | ~ v1_funct_2(C_150,A_149,B_148)
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(A_149,B_148))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_946,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_924])).

tff(c_964,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_371,c_946])).

tff(c_965,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_964])).

tff(c_261,plain,(
    ! [A_98,B_99,C_100] :
      ( k2_relset_1(A_98,B_99,C_100) = k2_relat_1(C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_281,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_261])).

tff(c_404,plain,(
    ! [A_118,B_119,C_120] :
      ( m1_subset_1(k2_relset_1(A_118,B_119,C_120),k1_zfmisc_1(B_119))
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_434,plain,
    ( m1_subset_1(k2_relat_1('#skF_6'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_404])).

tff(c_446,plain,(
    m1_subset_1(k2_relat_1('#skF_6'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_434])).

tff(c_48,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(A_42,B_43)
      | ~ m1_subset_1(A_42,k1_zfmisc_1(B_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_460,plain,(
    r1_tarski(k2_relat_1('#skF_6'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_446,c_48])).

tff(c_134,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_117])).

tff(c_66,plain,(
    v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_372,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_347])).

tff(c_949,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_7') = '#skF_4'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_924])).

tff(c_968,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_372,c_949])).

tff(c_990,plain,(
    k1_relat_1('#skF_7') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_968])).

tff(c_52,plain,(
    ! [A_44,B_46] :
      ( k1_relat_1(k5_relat_1(A_44,B_46)) = k1_relat_1(A_44)
      | ~ r1_tarski(k2_relat_1(A_44),k1_relat_1(B_46))
      | ~ v1_relat_1(B_46)
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_997,plain,(
    ! [A_44] :
      ( k1_relat_1(k5_relat_1(A_44,'#skF_7')) = k1_relat_1(A_44)
      | ~ r1_tarski(k2_relat_1(A_44),'#skF_4')
      | ~ v1_relat_1('#skF_7')
      | ~ v1_relat_1(A_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_990,c_52])).

tff(c_29684,plain,(
    ! [A_2764] :
      ( k1_relat_1(k5_relat_1(A_2764,'#skF_7')) = k1_relat_1(A_2764)
      | ~ r1_tarski(k2_relat_1(A_2764),'#skF_4')
      | ~ v1_relat_1(A_2764) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_997])).

tff(c_29729,plain,
    ( k1_relat_1(k5_relat_1('#skF_6','#skF_7')) = k1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_460,c_29684])).

tff(c_29763,plain,(
    k1_relat_1(k5_relat_1('#skF_6','#skF_7')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_965,c_29729])).

tff(c_29765,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8593,c_29763])).

tff(c_29766,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2897])).

tff(c_24,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_71,plain,(
    ! [A_54] :
      ( k1_xboole_0 = A_54
      | ~ v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_75,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_71])).

tff(c_76,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_24])).

tff(c_29809,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29766,c_76])).

tff(c_29813,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_29809])).

tff(c_29814,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_968])).

tff(c_29839,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29814,c_76])).

tff(c_29843,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_29839])).

tff(c_29845,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_38,plain,(
    ! [A_25,B_26] : m1_subset_1('#skF_2'(A_25,B_26),k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_29933,plain,(
    ! [A_2770,B_2771] :
      ( v1_xboole_0('#skF_2'(A_2770,B_2771))
      | ~ v1_xboole_0(B_2771) ) ),
    inference(resolution,[status(thm)],[c_38,c_190])).

tff(c_56,plain,(
    ! [A_50] :
      ( k1_xboole_0 = A_50
      | ~ v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_29859,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_29845,c_56])).

tff(c_29844,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_29852,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_29844,c_56])).

tff(c_29869,plain,(
    '#skF_7' = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29859,c_29852])).

tff(c_58,plain,(
    ! [B_52,A_51] :
      ( ~ v1_xboole_0(B_52)
      | B_52 = A_51
      | ~ v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_29851,plain,(
    ! [A_51] :
      ( A_51 = '#skF_7'
      | ~ v1_xboole_0(A_51) ) ),
    inference(resolution,[status(thm)],[c_29844,c_58])).

tff(c_29901,plain,(
    ! [A_51] :
      ( A_51 = '#skF_5'
      | ~ v1_xboole_0(A_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29869,c_29851])).

tff(c_29978,plain,(
    ! [A_2772,B_2773] :
      ( '#skF_2'(A_2772,B_2773) = '#skF_5'
      | ~ v1_xboole_0(B_2773) ) ),
    inference(resolution,[status(thm)],[c_29933,c_29901])).

tff(c_29985,plain,(
    ! [A_2774] : '#skF_2'(A_2774,'#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_29845,c_29978])).

tff(c_28,plain,(
    ! [A_25,B_26] : v1_funct_2('#skF_2'(A_25,B_26),A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_29999,plain,(
    ! [A_2774] : v1_funct_2('#skF_5',A_2774,'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_29985,c_28])).

tff(c_16,plain,(
    ! [B_9,A_8,C_10] :
      ( k1_xboole_0 = B_9
      | k1_relset_1(A_8,B_9,C_10) = A_8
      | ~ v1_funct_2(C_10,A_8,B_9)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_30803,plain,(
    ! [B_2839,A_2840,C_2841] :
      ( B_2839 = '#skF_5'
      | k1_relset_1(A_2840,B_2839,C_2841) = A_2840
      | ~ v1_funct_2(C_2841,A_2840,B_2839)
      | ~ m1_subset_1(C_2841,k1_zfmisc_1(k2_zfmisc_1(A_2840,B_2839))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29859,c_16])).

tff(c_30818,plain,(
    ! [B_26,A_25] :
      ( B_26 = '#skF_5'
      | k1_relset_1(A_25,B_26,'#skF_2'(A_25,B_26)) = A_25
      | ~ v1_funct_2('#skF_2'(A_25,B_26),A_25,B_26) ) ),
    inference(resolution,[status(thm)],[c_38,c_30803])).

tff(c_30924,plain,(
    ! [B_2850,A_2851] :
      ( B_2850 = '#skF_5'
      | k1_relset_1(A_2851,B_2850,'#skF_2'(A_2851,B_2850)) = A_2851 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30818])).

tff(c_18,plain,(
    ! [A_11,B_12,C_13] :
      ( m1_subset_1(k1_relset_1(A_11,B_12,C_13),k1_zfmisc_1(A_11))
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_30934,plain,(
    ! [A_2851,B_2850] :
      ( m1_subset_1(A_2851,k1_zfmisc_1(A_2851))
      | ~ m1_subset_1('#skF_2'(A_2851,B_2850),k1_zfmisc_1(k2_zfmisc_1(A_2851,B_2850)))
      | B_2850 = '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30924,c_18])).

tff(c_30953,plain,(
    ! [A_2851,B_2850] :
      ( m1_subset_1(A_2851,k1_zfmisc_1(A_2851))
      | B_2850 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_30934])).

tff(c_31001,plain,(
    ! [B_2855] : B_2855 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_30953])).

tff(c_29883,plain,(
    ~ v1_funct_2(k4_relset_1('#skF_3','#skF_4','#skF_4','#skF_5','#skF_6','#skF_5'),'#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29869,c_60])).

tff(c_31180,plain,(
    ~ v1_funct_2('#skF_5','#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_31001,c_29883])).

tff(c_31287,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_29999,c_31180])).

tff(c_31290,plain,(
    ! [A_4220] : m1_subset_1(A_4220,k1_zfmisc_1(A_4220)) ),
    inference(splitRight,[status(thm)],[c_30953])).

tff(c_4,plain,(
    ! [C_7,B_5,A_4] :
      ( v1_xboole_0(C_7)
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(B_5,A_4)))
      | ~ v1_xboole_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_31382,plain,(
    ! [B_4227,A_4228] :
      ( v1_xboole_0(k2_zfmisc_1(B_4227,A_4228))
      | ~ v1_xboole_0(A_4228) ) ),
    inference(resolution,[status(thm)],[c_31290,c_4])).

tff(c_171,plain,(
    ! [C_87,B_88,A_89] :
      ( ~ v1_xboole_0(C_87)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(C_87))
      | ~ r2_hidden(A_89,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_186,plain,(
    ! [A_89] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r2_hidden(A_89,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_64,c_171])).

tff(c_189,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_186])).

tff(c_31392,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_31382,c_189])).

tff(c_31404,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_29845,c_31392])).

tff(c_31430,plain,(
    ! [A_4232] : ~ r2_hidden(A_4232,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_31435,plain,(
    ! [A_40] :
      ( v1_xboole_0('#skF_7')
      | ~ m1_subset_1(A_40,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_46,c_31430])).

tff(c_31501,plain,(
    ! [A_4236] : ~ m1_subset_1(A_4236,'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_31435])).

tff(c_31506,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_26,c_31501])).

tff(c_31507,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_31435])).

tff(c_31518,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_31507,c_56])).

tff(c_31523,plain,(
    '#skF_7' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31518,c_89])).

tff(c_31627,plain,(
    ! [A_4243,B_4244] :
      ( v1_xboole_0('#skF_2'(A_4243,B_4244))
      | ~ v1_xboole_0(B_4244) ) ),
    inference(resolution,[status(thm)],[c_38,c_31407])).

tff(c_31517,plain,(
    ! [A_51] :
      ( A_51 = '#skF_7'
      | ~ v1_xboole_0(A_51) ) ),
    inference(resolution,[status(thm)],[c_31507,c_58])).

tff(c_31722,plain,(
    ! [A_4250,B_4251] :
      ( '#skF_2'(A_4250,B_4251) = '#skF_7'
      | ~ v1_xboole_0(B_4251) ) ),
    inference(resolution,[status(thm)],[c_31627,c_31517])).

tff(c_31754,plain,(
    ! [A_4253] : '#skF_2'(A_4253,'#skF_7') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_31507,c_31722])).

tff(c_31768,plain,(
    ! [A_4253] : v1_funct_2('#skF_7',A_4253,'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_31754,c_28])).

tff(c_31862,plain,(
    ! [A_4260] : m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(A_4260,'#skF_7'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_31754,c_38])).

tff(c_31880,plain,(
    ! [A_4260] : k1_relset_1(A_4260,'#skF_7','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_31862,c_40])).

tff(c_31765,plain,(
    ! [A_4253] : m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(A_4253,'#skF_7'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_31754,c_38])).

tff(c_14,plain,(
    ! [B_9,C_10] :
      ( k1_relset_1(k1_xboole_0,B_9,C_10) = k1_xboole_0
      | ~ v1_funct_2(C_10,k1_xboole_0,B_9)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_32013,plain,(
    ! [B_4266,C_4267] :
      ( k1_relset_1('#skF_7',B_4266,C_4267) = '#skF_7'
      | ~ v1_funct_2(C_4267,'#skF_7',B_4266)
      | ~ m1_subset_1(C_4267,k1_zfmisc_1(k2_zfmisc_1('#skF_7',B_4266))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31518,c_31518,c_31518,c_31518,c_14])).

tff(c_32021,plain,
    ( k1_relset_1('#skF_7','#skF_7','#skF_7') = '#skF_7'
    | ~ v1_funct_2('#skF_7','#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_31765,c_32013])).

tff(c_32045,plain,(
    k1_relat_1('#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31768,c_31880,c_32021])).

tff(c_31926,plain,(
    ! [A_4263] : k1_relset_1(A_4263,'#skF_7','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_31862,c_40])).

tff(c_31931,plain,(
    ! [A_4263] :
      ( m1_subset_1(k1_relat_1('#skF_7'),k1_zfmisc_1(A_4263))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(A_4263,'#skF_7'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31926,c_18])).

tff(c_31936,plain,(
    ! [A_4263] : m1_subset_1(k1_relat_1('#skF_7'),k1_zfmisc_1(A_4263)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31765,c_31931])).

tff(c_32112,plain,(
    ! [A_4270] : m1_subset_1('#skF_7',k1_zfmisc_1(A_4270)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32045,c_31936])).

tff(c_32136,plain,(
    ! [A_28,B_29] : k1_relset_1(A_28,B_29,'#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_32112,c_40])).

tff(c_32166,plain,(
    ! [A_28,B_29] : k1_relset_1(A_28,B_29,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32045,c_32136])).

tff(c_32056,plain,(
    ! [A_4263] : m1_subset_1('#skF_7',k1_zfmisc_1(A_4263)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32045,c_31936])).

tff(c_32447,plain,(
    ! [B_4285,A_4286,C_4287] :
      ( B_4285 = '#skF_7'
      | k1_relset_1(A_4286,B_4285,C_4287) = A_4286
      | ~ v1_funct_2(C_4287,A_4286,B_4285)
      | ~ m1_subset_1(C_4287,k1_zfmisc_1(k2_zfmisc_1(A_4286,B_4285))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31518,c_16])).

tff(c_32451,plain,(
    ! [B_4285,A_4286] :
      ( B_4285 = '#skF_7'
      | k1_relset_1(A_4286,B_4285,'#skF_7') = A_4286
      | ~ v1_funct_2('#skF_7',A_4286,B_4285) ) ),
    inference(resolution,[status(thm)],[c_32056,c_32447])).

tff(c_32840,plain,(
    ! [B_4327,A_4328] :
      ( B_4327 = '#skF_7'
      | A_4328 = '#skF_7'
      | ~ v1_funct_2('#skF_7',A_4328,B_4327) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32166,c_32451])).

tff(c_32855,plain,
    ( '#skF_7' = '#skF_5'
    | '#skF_7' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_66,c_32840])).

tff(c_32864,plain,(
    '#skF_7' = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_31523,c_32855])).

tff(c_32904,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32864,c_31507])).

tff(c_32910,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_31437,c_32904])).

tff(c_32912,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_31428])).

tff(c_33094,plain,(
    ! [A_4339,B_4340] :
      ( v1_xboole_0('#skF_2'(A_4339,B_4340))
      | ~ v1_xboole_0(B_4340) ) ),
    inference(resolution,[status(thm)],[c_38,c_31407])).

tff(c_32949,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_32912,c_56])).

tff(c_32911,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_31428])).

tff(c_32942,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_32911,c_56])).

tff(c_32967,plain,(
    '#skF_7' = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32949,c_32942])).

tff(c_32941,plain,(
    ! [A_51] :
      ( A_51 = '#skF_7'
      | ~ v1_xboole_0(A_51) ) ),
    inference(resolution,[status(thm)],[c_32911,c_58])).

tff(c_33006,plain,(
    ! [A_51] :
      ( A_51 = '#skF_5'
      | ~ v1_xboole_0(A_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32967,c_32941])).

tff(c_33163,plain,(
    ! [A_4344,B_4345] :
      ( '#skF_2'(A_4344,B_4345) = '#skF_5'
      | ~ v1_xboole_0(B_4345) ) ),
    inference(resolution,[status(thm)],[c_33094,c_33006])).

tff(c_33172,plain,(
    ! [A_4346] : '#skF_2'(A_4346,'#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_32912,c_33163])).

tff(c_33186,plain,(
    ! [A_4346] : v1_funct_2('#skF_5',A_4346,'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_33172,c_28])).

tff(c_33850,plain,(
    ! [B_4379,A_4380,C_4381] :
      ( B_4379 = '#skF_5'
      | k1_relset_1(A_4380,B_4379,C_4381) = A_4380
      | ~ v1_funct_2(C_4381,A_4380,B_4379)
      | ~ m1_subset_1(C_4381,k1_zfmisc_1(k2_zfmisc_1(A_4380,B_4379))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32949,c_16])).

tff(c_33868,plain,(
    ! [B_26,A_25] :
      ( B_26 = '#skF_5'
      | k1_relset_1(A_25,B_26,'#skF_2'(A_25,B_26)) = A_25
      | ~ v1_funct_2('#skF_2'(A_25,B_26),A_25,B_26) ) ),
    inference(resolution,[status(thm)],[c_38,c_33850])).

tff(c_34218,plain,(
    ! [B_4420,A_4421] :
      ( B_4420 = '#skF_5'
      | k1_relset_1(A_4421,B_4420,'#skF_2'(A_4421,B_4420)) = A_4421 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_33868])).

tff(c_34228,plain,(
    ! [A_4421,B_4420] :
      ( m1_subset_1(A_4421,k1_zfmisc_1(A_4421))
      | ~ m1_subset_1('#skF_2'(A_4421,B_4420),k1_zfmisc_1(k2_zfmisc_1(A_4421,B_4420)))
      | B_4420 = '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34218,c_18])).

tff(c_34244,plain,(
    ! [A_4421,B_4420] :
      ( m1_subset_1(A_4421,k1_zfmisc_1(A_4421))
      | B_4420 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34228])).

tff(c_34251,plain,(
    ! [B_4422] : B_4422 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_34244])).

tff(c_32978,plain,(
    ~ v1_funct_2(k4_relset_1('#skF_3','#skF_4','#skF_4','#skF_5','#skF_6','#skF_5'),'#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32967,c_60])).

tff(c_34414,plain,(
    ~ v1_funct_2('#skF_5','#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_34251,c_32978])).

tff(c_34531,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_33186,c_34414])).

tff(c_34571,plain,(
    ! [A_5878] : m1_subset_1(A_5878,k1_zfmisc_1(A_5878)) ),
    inference(splitRight,[status(thm)],[c_34244])).

tff(c_34750,plain,(
    ! [B_5890,A_5891] :
      ( v1_xboole_0(k2_zfmisc_1(B_5890,A_5891))
      | ~ v1_xboole_0(A_5891) ) ),
    inference(resolution,[status(thm)],[c_34571,c_4])).

tff(c_34773,plain,(
    ! [B_5892,A_5893] :
      ( k2_zfmisc_1(B_5892,A_5893) = '#skF_5'
      | ~ v1_xboole_0(A_5893) ) ),
    inference(resolution,[status(thm)],[c_34750,c_33006])).

tff(c_34785,plain,(
    ! [B_5892] : k2_zfmisc_1(B_5892,'#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_32912,c_34773])).

tff(c_33169,plain,(
    ! [A_4344] : '#skF_2'(A_4344,'#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_32912,c_33163])).

tff(c_34187,plain,(
    ! [B_4418,D_4415,A_4414,F_4416,C_4419,E_4417] :
      ( k4_relset_1(A_4414,B_4418,C_4419,D_4415,E_4417,F_4416) = k5_relat_1(E_4417,F_4416)
      | ~ m1_subset_1(F_4416,k1_zfmisc_1(k2_zfmisc_1(C_4419,D_4415)))
      | ~ m1_subset_1(E_4417,k1_zfmisc_1(k2_zfmisc_1(A_4414,B_4418))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_39145,plain,(
    ! [B_6127,E_6125,A_6124,A_6128,B_6126] :
      ( k4_relset_1(A_6128,B_6126,A_6124,B_6127,E_6125,'#skF_2'(A_6124,B_6127)) = k5_relat_1(E_6125,'#skF_2'(A_6124,B_6127))
      | ~ m1_subset_1(E_6125,k1_zfmisc_1(k2_zfmisc_1(A_6128,B_6126))) ) ),
    inference(resolution,[status(thm)],[c_38,c_34187])).

tff(c_39297,plain,(
    ! [A_6133,B_6134] : k4_relset_1('#skF_3','#skF_4',A_6133,B_6134,'#skF_6','#skF_2'(A_6133,B_6134)) = k5_relat_1('#skF_6','#skF_2'(A_6133,B_6134)) ),
    inference(resolution,[status(thm)],[c_68,c_39145])).

tff(c_39303,plain,(
    ! [A_6133,B_6134] :
      ( m1_subset_1(k5_relat_1('#skF_6','#skF_2'(A_6133,B_6134)),k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_6134)))
      | ~ m1_subset_1('#skF_2'(A_6133,B_6134),k1_zfmisc_1(k2_zfmisc_1(A_6133,B_6134)))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39297,c_22])).

tff(c_39321,plain,(
    ! [A_6135,B_6136] : m1_subset_1(k5_relat_1('#skF_6','#skF_2'(A_6135,B_6136)),k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_6136))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_38,c_39303])).

tff(c_39384,plain,(
    m1_subset_1(k5_relat_1('#skF_6','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_33169,c_39321])).

tff(c_39401,plain,(
    m1_subset_1(k5_relat_1('#skF_6','#skF_5'),k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34785,c_39384])).

tff(c_31406,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_33007,plain,(
    ! [A_4334] :
      ( A_4334 = '#skF_5'
      | ~ v1_xboole_0(A_4334) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32967,c_32941])).

tff(c_33014,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_31406,c_33007])).

tff(c_33029,plain,(
    ! [C_7] :
      ( v1_xboole_0(C_7)
      | ~ m1_subset_1(C_7,k1_zfmisc_1('#skF_5'))
      | ~ v1_xboole_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33014,c_4])).

tff(c_33047,plain,(
    ! [C_7] :
      ( v1_xboole_0(C_7)
      | ~ m1_subset_1(C_7,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32912,c_33029])).

tff(c_39446,plain,(
    v1_xboole_0(k5_relat_1('#skF_6','#skF_5')) ),
    inference(resolution,[status(thm)],[c_39401,c_33047])).

tff(c_39539,plain,(
    k5_relat_1('#skF_6','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_39446,c_33006])).

tff(c_33183,plain,(
    ! [A_4346] : m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_4346,'#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_33172,c_38])).

tff(c_33383,plain,(
    ! [A_4358] : m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_4358,'#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_33172,c_38])).

tff(c_33423,plain,(
    ! [A_4359] : k1_relset_1(A_4359,'#skF_5','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_33383,c_40])).

tff(c_33428,plain,(
    ! [A_4359] :
      ( m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1(A_4359))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_4359,'#skF_5'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33423,c_18])).

tff(c_33435,plain,(
    ! [A_4360] : m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1(A_4360)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33183,c_33428])).

tff(c_33471,plain,(
    v1_xboole_0(k1_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_33435,c_33047])).

tff(c_33525,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_33471,c_33006])).

tff(c_33477,plain,(
    ! [A_4360] : r1_tarski(k1_relat_1('#skF_5'),A_4360) ),
    inference(resolution,[status(thm)],[c_33435,c_48])).

tff(c_33616,plain,(
    ! [A_4360] : r1_tarski('#skF_5',A_4360) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33525,c_33477])).

tff(c_50,plain,(
    ! [A_42,B_43] :
      ( m1_subset_1(A_42,k1_zfmisc_1(B_43))
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_39658,plain,(
    ! [D_6153,A_6154,C_6155,B_6152,A_6151,E_6150] :
      ( k4_relset_1(A_6154,B_6152,C_6155,D_6153,E_6150,A_6151) = k5_relat_1(E_6150,A_6151)
      | ~ m1_subset_1(E_6150,k1_zfmisc_1(k2_zfmisc_1(A_6154,B_6152)))
      | ~ r1_tarski(A_6151,k2_zfmisc_1(C_6155,D_6153)) ) ),
    inference(resolution,[status(thm)],[c_50,c_34187])).

tff(c_39726,plain,(
    ! [C_6156,D_6157,A_6158] :
      ( k4_relset_1('#skF_3','#skF_4',C_6156,D_6157,'#skF_6',A_6158) = k5_relat_1('#skF_6',A_6158)
      | ~ r1_tarski(A_6158,k2_zfmisc_1(C_6156,D_6157)) ) ),
    inference(resolution,[status(thm)],[c_68,c_39658])).

tff(c_39777,plain,(
    ! [C_6156,D_6157] : k4_relset_1('#skF_3','#skF_4',C_6156,D_6157,'#skF_6','#skF_5') = k5_relat_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_33616,c_39726])).

tff(c_39799,plain,(
    ! [C_6156,D_6157] : k4_relset_1('#skF_3','#skF_4',C_6156,D_6157,'#skF_6','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_39539,c_39777])).

tff(c_39988,plain,(
    ~ v1_funct_2('#skF_5','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_39799,c_32978])).

tff(c_39991,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_33186,c_39988])).

tff(c_39993,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_39994,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_39993,c_76])).

tff(c_55205,plain,(
    ! [C_20399,B_20400,A_20401] :
      ( v1_xboole_0(C_20399)
      | ~ m1_subset_1(C_20399,k1_zfmisc_1(k2_zfmisc_1(B_20400,A_20401)))
      | ~ v1_xboole_0(A_20401) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_55429,plain,(
    ! [A_20411,B_20412] :
      ( v1_xboole_0('#skF_2'(A_20411,B_20412))
      | ~ v1_xboole_0(B_20412) ) ),
    inference(resolution,[status(thm)],[c_38,c_55205])).

tff(c_39996,plain,(
    ! [A_50] :
      ( A_50 = '#skF_4'
      | ~ v1_xboole_0(A_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39993,c_56])).

tff(c_55441,plain,(
    ! [A_20413,B_20414] :
      ( '#skF_2'(A_20413,B_20414) = '#skF_4'
      | ~ v1_xboole_0(B_20414) ) ),
    inference(resolution,[status(thm)],[c_55429,c_39996])).

tff(c_55452,plain,(
    ! [A_20415] : '#skF_2'(A_20415,'#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_39994,c_55441])).

tff(c_55466,plain,(
    ! [A_20415] : v1_funct_2('#skF_4',A_20415,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_55452,c_28])).

tff(c_55463,plain,(
    ! [A_20415] : m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_20415,'#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_55452,c_38])).

tff(c_55676,plain,(
    ! [A_20429] : m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_20429,'#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_55452,c_38])).

tff(c_55727,plain,(
    ! [A_20430] : k1_relset_1(A_20430,'#skF_4','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_55676,c_40])).

tff(c_55732,plain,(
    ! [A_20430] :
      ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1(A_20430))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_20430,'#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55727,c_18])).

tff(c_55784,plain,(
    ! [A_20433] : m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1(A_20433)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55463,c_55732])).

tff(c_43732,plain,(
    ! [C_10185,B_10186,A_10187] :
      ( v1_xboole_0(C_10185)
      | ~ m1_subset_1(C_10185,k1_zfmisc_1(k2_zfmisc_1(B_10186,A_10187)))
      | ~ v1_xboole_0(A_10187) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_43845,plain,(
    ! [A_10194,B_10195] :
      ( v1_xboole_0('#skF_2'(A_10194,B_10195))
      | ~ v1_xboole_0(B_10195) ) ),
    inference(resolution,[status(thm)],[c_38,c_43732])).

tff(c_43853,plain,(
    ! [A_10196,B_10197] :
      ( '#skF_2'(A_10196,B_10197) = '#skF_4'
      | ~ v1_xboole_0(B_10197) ) ),
    inference(resolution,[status(thm)],[c_43845,c_39996])).

tff(c_43874,plain,(
    ! [A_10199] : '#skF_2'(A_10199,'#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_39994,c_43853])).

tff(c_43885,plain,(
    ! [A_10199] : m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_10199,'#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_43874,c_38])).

tff(c_40130,plain,(
    ! [C_6211,B_6212,A_6213] :
      ( v1_xboole_0(C_6211)
      | ~ m1_subset_1(C_6211,k1_zfmisc_1(k2_zfmisc_1(B_6212,A_6213)))
      | ~ v1_xboole_0(A_6213) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_42501,plain,(
    ! [A_9030,B_9031] :
      ( v1_xboole_0('#skF_2'(A_9030,B_9031))
      | ~ v1_xboole_0(B_9031) ) ),
    inference(resolution,[status(thm)],[c_38,c_40130])).

tff(c_42509,plain,(
    ! [A_9032,B_9033] :
      ( '#skF_2'(A_9032,B_9033) = '#skF_4'
      | ~ v1_xboole_0(B_9033) ) ),
    inference(resolution,[status(thm)],[c_42501,c_39996])).

tff(c_42516,plain,(
    ! [A_9034] : '#skF_2'(A_9034,'#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_39994,c_42509])).

tff(c_42530,plain,(
    ! [A_9034] : v1_funct_2('#skF_4',A_9034,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_42516,c_28])).

tff(c_43128,plain,(
    ! [B_9075,A_9076,C_9077] :
      ( B_9075 = '#skF_4'
      | k1_relset_1(A_9076,B_9075,C_9077) = A_9076
      | ~ v1_funct_2(C_9077,A_9076,B_9075)
      | ~ m1_subset_1(C_9077,k1_zfmisc_1(k2_zfmisc_1(A_9076,B_9075))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39993,c_16])).

tff(c_43143,plain,(
    ! [B_26,A_25] :
      ( B_26 = '#skF_4'
      | k1_relset_1(A_25,B_26,'#skF_2'(A_25,B_26)) = A_25
      | ~ v1_funct_2('#skF_2'(A_25,B_26),A_25,B_26) ) ),
    inference(resolution,[status(thm)],[c_38,c_43128])).

tff(c_43406,plain,(
    ! [B_9115,A_9116] :
      ( B_9115 = '#skF_4'
      | k1_relset_1(A_9116,B_9115,'#skF_2'(A_9116,B_9115)) = A_9116 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_43143])).

tff(c_43416,plain,(
    ! [A_9116,B_9115] :
      ( m1_subset_1(A_9116,k1_zfmisc_1(A_9116))
      | ~ m1_subset_1('#skF_2'(A_9116,B_9115),k1_zfmisc_1(k2_zfmisc_1(A_9116,B_9115)))
      | B_9115 = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_43406,c_18])).

tff(c_43432,plain,(
    ! [A_9116,B_9115] :
      ( m1_subset_1(A_9116,k1_zfmisc_1(A_9116))
      | B_9115 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_43416])).

tff(c_43439,plain,(
    ! [B_9117] : B_9117 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_43432])).

tff(c_41016,plain,(
    ! [B_6273,A_6274,C_6275] :
      ( B_6273 = '#skF_4'
      | k1_relset_1(A_6274,B_6273,C_6275) = A_6274
      | ~ v1_funct_2(C_6275,A_6274,B_6273)
      | ~ m1_subset_1(C_6275,k1_zfmisc_1(k2_zfmisc_1(A_6274,B_6273))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39993,c_16])).

tff(c_41035,plain,(
    ! [B_26,A_25] :
      ( B_26 = '#skF_4'
      | k1_relset_1(A_25,B_26,'#skF_2'(A_25,B_26)) = A_25
      | ~ v1_funct_2('#skF_2'(A_25,B_26),A_25,B_26) ) ),
    inference(resolution,[status(thm)],[c_38,c_41016])).

tff(c_42022,plain,(
    ! [B_7627,A_7628] :
      ( B_7627 = '#skF_4'
      | k1_relset_1(A_7628,B_7627,'#skF_2'(A_7628,B_7627)) = A_7628 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_41035])).

tff(c_42032,plain,(
    ! [A_7628,B_7627] :
      ( m1_subset_1(A_7628,k1_zfmisc_1(A_7628))
      | ~ m1_subset_1('#skF_2'(A_7628,B_7627),k1_zfmisc_1(k2_zfmisc_1(A_7628,B_7627)))
      | B_7627 = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42022,c_18])).

tff(c_42048,plain,(
    ! [A_7628,B_7627] :
      ( m1_subset_1(A_7628,k1_zfmisc_1(A_7628))
      | B_7627 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_42032])).

tff(c_42055,plain,(
    ! [B_7629] : B_7629 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_42048])).

tff(c_40153,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_40130])).

tff(c_40173,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_40153])).

tff(c_42191,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_42055,c_40173])).

tff(c_42293,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_39994,c_42191])).

tff(c_42295,plain,(
    ! [A_9016] : m1_subset_1(A_9016,k1_zfmisc_1(A_9016)) ),
    inference(splitRight,[status(thm)],[c_42048])).

tff(c_42383,plain,(
    ! [B_9024,A_9025] :
      ( v1_xboole_0(k2_zfmisc_1(B_9024,A_9025))
      | ~ v1_xboole_0(A_9025) ) ),
    inference(resolution,[status(thm)],[c_42295,c_4])).

tff(c_39992,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_40005,plain,
    ( '#skF_5' = '#skF_4'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_39993,c_39993,c_39992])).

tff(c_40006,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_40005])).

tff(c_40020,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40006,c_68])).

tff(c_40078,plain,(
    ! [C_6198,B_6199,A_6200] :
      ( ~ v1_xboole_0(C_6198)
      | ~ m1_subset_1(B_6199,k1_zfmisc_1(C_6198))
      | ~ r2_hidden(A_6200,B_6199) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_40092,plain,(
    ! [A_6200] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_4'))
      | ~ r2_hidden(A_6200,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_40020,c_40078])).

tff(c_40125,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_40092])).

tff(c_42390,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_42383,c_40125])).

tff(c_42404,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_39994,c_42390])).

tff(c_42406,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_40153])).

tff(c_42426,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_42406,c_39996])).

tff(c_42405,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_40153])).

tff(c_42419,plain,(
    '#skF_7' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_42405,c_39996])).

tff(c_40140,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_40020,c_40130])).

tff(c_40152,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_39994,c_40140])).

tff(c_40161,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40152,c_39996])).

tff(c_40046,plain,(
    ~ v1_funct_2(k4_relset_1('#skF_4','#skF_4','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40006,c_40006,c_60])).

tff(c_40164,plain,(
    ~ v1_funct_2(k4_relset_1('#skF_4','#skF_4','#skF_4','#skF_5','#skF_4','#skF_7'),'#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40161,c_40046])).

tff(c_42680,plain,(
    ~ v1_funct_2(k4_relset_1('#skF_4','#skF_4','#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42426,c_42426,c_42419,c_40164])).

tff(c_43489,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_43439,c_42680])).

tff(c_43569,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42530,c_43489])).

tff(c_43571,plain,(
    ! [A_10174] : m1_subset_1(A_10174,k1_zfmisc_1(A_10174)) ),
    inference(splitRight,[status(thm)],[c_43432])).

tff(c_43668,plain,(
    ! [B_10182,A_10183] :
      ( v1_xboole_0(k2_zfmisc_1(B_10182,A_10183))
      | ~ v1_xboole_0(A_10183) ) ),
    inference(resolution,[status(thm)],[c_43571,c_4])).

tff(c_43675,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_43668,c_40125])).

tff(c_43686,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_39994,c_43675])).

tff(c_43689,plain,(
    ! [A_10184] : ~ r2_hidden(A_10184,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_40092])).

tff(c_43694,plain,(
    ! [A_40] :
      ( v1_xboole_0('#skF_6')
      | ~ m1_subset_1(A_40,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_46,c_43689])).

tff(c_43758,plain,(
    ! [A_10188] : ~ m1_subset_1(A_10188,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_43694])).

tff(c_43763,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_26,c_43758])).

tff(c_43764,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_43694])).

tff(c_43771,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_43764,c_39996])).

tff(c_43688,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_40092])).

tff(c_43701,plain,(
    k2_zfmisc_1('#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_43688,c_39996])).

tff(c_43704,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43701,c_40020])).

tff(c_43773,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43771,c_43704])).

tff(c_43784,plain,(
    ! [A_10189,B_10190,C_10191] :
      ( k1_relset_1(A_10189,B_10190,C_10191) = k1_relat_1(C_10191)
      | ~ m1_subset_1(C_10191,k1_zfmisc_1(k2_zfmisc_1(A_10189,B_10190))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_43980,plain,(
    ! [C_10208] :
      ( k1_relset_1('#skF_4','#skF_4',C_10208) = k1_relat_1(C_10208)
      | ~ m1_subset_1(C_10208,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_43701,c_43784])).

tff(c_43992,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_43773,c_43980])).

tff(c_44073,plain,(
    ! [A_10211,B_10212,C_10213] :
      ( m1_subset_1(k1_relset_1(A_10211,B_10212,C_10213),k1_zfmisc_1(A_10211))
      | ~ m1_subset_1(C_10213,k1_zfmisc_1(k2_zfmisc_1(A_10211,B_10212))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_44109,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_43992,c_44073])).

tff(c_44123,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43773,c_43701,c_44109])).

tff(c_43735,plain,(
    ! [C_10185] :
      ( v1_xboole_0(C_10185)
      | ~ m1_subset_1(C_10185,k1_zfmisc_1('#skF_4'))
      | ~ v1_xboole_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_43701,c_43732])).

tff(c_43751,plain,(
    ! [C_10185] :
      ( v1_xboole_0(C_10185)
      | ~ m1_subset_1(C_10185,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39994,c_43735])).

tff(c_44196,plain,(
    v1_xboole_0(k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_44123,c_43751])).

tff(c_44211,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_44196,c_39996])).

tff(c_44038,plain,(
    ! [A_10210] : m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_10210,'#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_43874,c_38])).

tff(c_44059,plain,(
    ! [A_10210] : k1_relset_1(A_10210,'#skF_4','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44038,c_40])).

tff(c_44344,plain,(
    ! [A_10219] : k1_relset_1(A_10219,'#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44211,c_44059])).

tff(c_44349,plain,(
    ! [A_10219] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(A_10219))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_10219,'#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44344,c_18])).

tff(c_44354,plain,(
    ! [A_10219] : m1_subset_1('#skF_4',k1_zfmisc_1(A_10219)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43885,c_44349])).

tff(c_45572,plain,(
    ! [D_11633,F_11634,E_11635,C_11637,B_11636,A_11632] :
      ( k4_relset_1(A_11632,B_11636,C_11637,D_11633,E_11635,F_11634) = k5_relat_1(E_11635,F_11634)
      | ~ m1_subset_1(F_11634,k1_zfmisc_1(k2_zfmisc_1(C_11637,D_11633)))
      | ~ m1_subset_1(E_11635,k1_zfmisc_1(k2_zfmisc_1(A_11632,B_11636))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_45793,plain,(
    ! [A_11647,B_11648,E_11649] :
      ( k4_relset_1(A_11647,B_11648,'#skF_4','#skF_5',E_11649,'#skF_7') = k5_relat_1(E_11649,'#skF_7')
      | ~ m1_subset_1(E_11649,k1_zfmisc_1(k2_zfmisc_1(A_11647,B_11648))) ) ),
    inference(resolution,[status(thm)],[c_64,c_45572])).

tff(c_45834,plain,(
    ! [A_11647,B_11648] : k4_relset_1(A_11647,B_11648,'#skF_4','#skF_5','#skF_4','#skF_7') = k5_relat_1('#skF_4','#skF_7') ),
    inference(resolution,[status(thm)],[c_44354,c_45793])).

tff(c_43777,plain,(
    ~ v1_funct_2(k4_relset_1('#skF_4','#skF_4','#skF_4','#skF_5','#skF_4','#skF_7'),'#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_43771,c_40046])).

tff(c_46593,plain,(
    ~ v1_funct_2(k5_relat_1('#skF_4','#skF_7'),'#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_45834,c_43777])).

tff(c_46594,plain,(
    ! [A_11694,B_11695] : k4_relset_1(A_11694,B_11695,'#skF_4','#skF_5','#skF_4','#skF_7') = k5_relat_1('#skF_4','#skF_7') ),
    inference(resolution,[status(thm)],[c_44354,c_45793])).

tff(c_46599,plain,(
    ! [A_11694,B_11695] :
      ( m1_subset_1(k5_relat_1('#skF_4','#skF_7'),k1_zfmisc_1(k2_zfmisc_1(A_11694,'#skF_5')))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_11694,B_11695))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46594,c_22])).

tff(c_46749,plain,(
    ! [A_11707] : m1_subset_1(k5_relat_1('#skF_4','#skF_7'),k1_zfmisc_1(k2_zfmisc_1(A_11707,'#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44354,c_64,c_46599])).

tff(c_10,plain,(
    ! [C_10,B_9] :
      ( v1_funct_2(C_10,k1_xboole_0,B_9)
      | k1_relset_1(k1_xboole_0,B_9,C_10) != k1_xboole_0
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_44483,plain,(
    ! [C_10,B_9] :
      ( v1_funct_2(C_10,'#skF_4',B_9)
      | k1_relset_1('#skF_4',B_9,C_10) != '#skF_4'
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_9))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39993,c_39993,c_39993,c_39993,c_10])).

tff(c_46768,plain,
    ( v1_funct_2(k5_relat_1('#skF_4','#skF_7'),'#skF_4','#skF_5')
    | k1_relset_1('#skF_4','#skF_5',k5_relat_1('#skF_4','#skF_7')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_46749,c_44483])).

tff(c_46793,plain,(
    k1_relset_1('#skF_4','#skF_5',k5_relat_1('#skF_4','#skF_7')) != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_46593,c_46768])).

tff(c_46604,plain,(
    ! [A_11694] : m1_subset_1(k5_relat_1('#skF_4','#skF_7'),k1_zfmisc_1(k2_zfmisc_1(A_11694,'#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44354,c_64,c_46599])).

tff(c_47725,plain,(
    ! [A_11762,B_11763,C_11764] :
      ( r1_tarski(k1_relset_1(A_11762,B_11763,C_11764),A_11762)
      | ~ m1_subset_1(C_11764,k1_zfmisc_1(k2_zfmisc_1(A_11762,B_11763))) ) ),
    inference(resolution,[status(thm)],[c_44073,c_48])).

tff(c_48117,plain,(
    ! [A_11776] : r1_tarski(k1_relset_1(A_11776,'#skF_5',k5_relat_1('#skF_4','#skF_7')),A_11776) ),
    inference(resolution,[status(thm)],[c_46604,c_47725])).

tff(c_43964,plain,(
    ! [C_10207] :
      ( v1_xboole_0(C_10207)
      | ~ m1_subset_1(C_10207,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39994,c_43735])).

tff(c_43978,plain,(
    ! [A_42] :
      ( v1_xboole_0(A_42)
      | ~ r1_tarski(A_42,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_50,c_43964])).

tff(c_48156,plain,(
    v1_xboole_0(k1_relset_1('#skF_4','#skF_5',k5_relat_1('#skF_4','#skF_7'))) ),
    inference(resolution,[status(thm)],[c_48117,c_43978])).

tff(c_48249,plain,(
    k1_relset_1('#skF_4','#skF_5',k5_relat_1('#skF_4','#skF_7')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_48156,c_39996])).

tff(c_48259,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46793,c_48249])).

tff(c_48261,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_40005])).

tff(c_53095,plain,(
    ! [A_17319,B_17320,C_17321] :
      ( k1_relset_1(A_17319,B_17320,C_17321) = k1_relat_1(C_17321)
      | ~ m1_subset_1(C_17321,k1_zfmisc_1(k2_zfmisc_1(A_17319,B_17320))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_53114,plain,(
    ! [A_25,B_26] : k1_relset_1(A_25,B_26,'#skF_2'(A_25,B_26)) = k1_relat_1('#skF_2'(A_25,B_26)) ),
    inference(resolution,[status(thm)],[c_38,c_53095])).

tff(c_54264,plain,(
    ! [B_17400,A_17401,C_17402] :
      ( B_17400 = '#skF_4'
      | k1_relset_1(A_17401,B_17400,C_17402) = A_17401
      | ~ v1_funct_2(C_17402,A_17401,B_17400)
      | ~ m1_subset_1(C_17402,k1_zfmisc_1(k2_zfmisc_1(A_17401,B_17400))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39993,c_16])).

tff(c_54282,plain,(
    ! [B_26,A_25] :
      ( B_26 = '#skF_4'
      | k1_relset_1(A_25,B_26,'#skF_2'(A_25,B_26)) = A_25
      | ~ v1_funct_2('#skF_2'(A_25,B_26),A_25,B_26) ) ),
    inference(resolution,[status(thm)],[c_38,c_54264])).

tff(c_54297,plain,(
    ! [B_26,A_25] :
      ( B_26 = '#skF_4'
      | k1_relat_1('#skF_2'(A_25,B_26)) = A_25 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_53114,c_54282])).

tff(c_54214,plain,(
    ! [A_17397,B_17398] : k1_relset_1(A_17397,B_17398,'#skF_2'(A_17397,B_17398)) = k1_relat_1('#skF_2'(A_17397,B_17398)) ),
    inference(resolution,[status(thm)],[c_38,c_53095])).

tff(c_54224,plain,(
    ! [A_17397,B_17398] :
      ( m1_subset_1(k1_relat_1('#skF_2'(A_17397,B_17398)),k1_zfmisc_1(A_17397))
      | ~ m1_subset_1('#skF_2'(A_17397,B_17398),k1_zfmisc_1(k2_zfmisc_1(A_17397,B_17398))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54214,c_18])).

tff(c_54335,plain,(
    ! [A_17405,B_17406] : m1_subset_1(k1_relat_1('#skF_2'(A_17405,B_17406)),k1_zfmisc_1(A_17405)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_54224])).

tff(c_54411,plain,(
    ! [A_25,B_26] :
      ( m1_subset_1(A_25,k1_zfmisc_1(A_25))
      | B_26 = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54297,c_54335])).

tff(c_54801,plain,(
    ! [B_18873] : B_18873 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_54411])).

tff(c_52871,plain,(
    ! [C_17303,B_17304,A_17305] :
      ( v1_xboole_0(C_17303)
      | ~ m1_subset_1(C_17303,k1_zfmisc_1(k2_zfmisc_1(B_17304,A_17305)))
      | ~ v1_xboole_0(A_17305) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_52884,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_52871])).

tff(c_52895,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_39994,c_52884])).

tff(c_52903,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_52895,c_39996])).

tff(c_52908,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52903,c_68])).

tff(c_53113,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52908,c_53095])).

tff(c_53293,plain,(
    ! [A_17330,B_17331,C_17332] :
      ( m1_subset_1(k1_relset_1(A_17330,B_17331,C_17332),k1_zfmisc_1(A_17330))
      | ~ m1_subset_1(C_17332,k1_zfmisc_1(k2_zfmisc_1(A_17330,B_17331))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_53325,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_53113,c_53293])).

tff(c_53335,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52908,c_53325])).

tff(c_54,plain,(
    ! [C_49,B_48,A_47] :
      ( ~ v1_xboole_0(C_49)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(C_49))
      | ~ r2_hidden(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_53341,plain,(
    ! [A_47] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_47,k1_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_53335,c_54])).

tff(c_53352,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_53341])).

tff(c_54886,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_54801,c_53352])).

tff(c_54993,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_39994,c_54886])).

tff(c_54995,plain,(
    ! [A_20392] : m1_subset_1(A_20392,k1_zfmisc_1(A_20392)) ),
    inference(splitRight,[status(thm)],[c_54411])).

tff(c_55153,plain,(
    ! [B_20396,A_20397] :
      ( v1_xboole_0(k2_zfmisc_1(B_20396,A_20397))
      | ~ v1_xboole_0(A_20397) ) ),
    inference(resolution,[status(thm)],[c_54995,c_4])).

tff(c_48356,plain,(
    ! [C_11808,B_11809,A_11810] :
      ( ~ v1_xboole_0(C_11808)
      | ~ m1_subset_1(B_11809,k1_zfmisc_1(C_11808))
      | ~ r2_hidden(A_11810,B_11809) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_48371,plain,(
    ! [A_11810] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r2_hidden(A_11810,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_68,c_48356])).

tff(c_52833,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_48371])).

tff(c_55160,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_55153,c_52833])).

tff(c_55174,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_39994,c_55160])).

tff(c_55176,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_53341])).

tff(c_55183,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_55176,c_39996])).

tff(c_55189,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48261,c_55183])).

tff(c_55191,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_48371])).

tff(c_55264,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_55191,c_39996])).

tff(c_55307,plain,(
    ! [C_7] :
      ( v1_xboole_0(C_7)
      | ~ m1_subset_1(C_7,k1_zfmisc_1('#skF_4'))
      | ~ v1_xboole_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55264,c_4])).

tff(c_55323,plain,(
    ! [C_7] :
      ( v1_xboole_0(C_7)
      | ~ m1_subset_1(C_7,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39994,c_55307])).

tff(c_55825,plain,(
    v1_xboole_0(k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_55784,c_55323])).

tff(c_55841,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_55825,c_39996])).

tff(c_55737,plain,(
    ! [A_20430] : m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1(A_20430)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55463,c_55732])).

tff(c_55876,plain,(
    ! [A_20430] : m1_subset_1('#skF_4',k1_zfmisc_1(A_20430)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55841,c_55737])).

tff(c_56233,plain,(
    ! [B_20452,A_20453,C_20454] :
      ( B_20452 = '#skF_4'
      | k1_relset_1(A_20453,B_20452,C_20454) = A_20453
      | ~ v1_funct_2(C_20454,A_20453,B_20452)
      | ~ m1_subset_1(C_20454,k1_zfmisc_1(k2_zfmisc_1(A_20453,B_20452))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39993,c_16])).

tff(c_56254,plain,(
    ! [B_26,A_25] :
      ( B_26 = '#skF_4'
      | k1_relset_1(A_25,B_26,'#skF_2'(A_25,B_26)) = A_25
      | ~ v1_funct_2('#skF_2'(A_25,B_26),A_25,B_26) ) ),
    inference(resolution,[status(thm)],[c_38,c_56233])).

tff(c_56515,plain,(
    ! [B_20482,A_20483] :
      ( B_20482 = '#skF_4'
      | k1_relset_1(A_20483,B_20482,'#skF_2'(A_20483,B_20482)) = A_20483 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_56254])).

tff(c_56525,plain,(
    ! [A_20483,B_20482] :
      ( m1_subset_1(A_20483,k1_zfmisc_1(A_20483))
      | ~ m1_subset_1('#skF_2'(A_20483,B_20482),k1_zfmisc_1(k2_zfmisc_1(A_20483,B_20482)))
      | B_20482 = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56515,c_18])).

tff(c_56541,plain,(
    ! [A_20483,B_20482] :
      ( m1_subset_1(A_20483,k1_zfmisc_1(A_20483))
      | B_20482 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_56525])).

tff(c_56576,plain,(
    ! [B_20490] : B_20490 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_56541])).

tff(c_55218,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_55205])).

tff(c_55230,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_39994,c_55218])).

tff(c_55245,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_55230,c_39996])).

tff(c_48260,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_40005])).

tff(c_48279,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48260,c_64])).

tff(c_55215,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_48279,c_55205])).

tff(c_55227,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_39994,c_55215])).

tff(c_55238,plain,(
    '#skF_7' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_55227,c_39996])).

tff(c_48320,plain,(
    ~ v1_funct_2(k4_relset_1('#skF_3','#skF_4','#skF_4','#skF_4','#skF_6','#skF_7'),'#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48260,c_48260,c_60])).

tff(c_55248,plain,(
    ~ v1_funct_2(k4_relset_1('#skF_3','#skF_4','#skF_4','#skF_4','#skF_6','#skF_4'),'#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55238,c_48320])).

tff(c_55439,plain,(
    ~ v1_funct_2(k4_relset_1('#skF_3','#skF_4','#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55245,c_55248])).

tff(c_56638,plain,(
    ~ v1_funct_2('#skF_4','#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_56576,c_55439])).

tff(c_56710,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_55466,c_56638])).

tff(c_56711,plain,(
    ! [A_20483] : m1_subset_1(A_20483,k1_zfmisc_1(A_20483)) ),
    inference(splitRight,[status(thm)],[c_56541])).

tff(c_56547,plain,(
    ! [F_20486,A_20484,E_20487,B_20488,D_20485,C_20489] :
      ( k4_relset_1(A_20484,B_20488,C_20489,D_20485,E_20487,F_20486) = k5_relat_1(E_20487,F_20486)
      | ~ m1_subset_1(F_20486,k1_zfmisc_1(k2_zfmisc_1(C_20489,D_20485)))
      | ~ m1_subset_1(E_20487,k1_zfmisc_1(k2_zfmisc_1(A_20484,B_20488))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_56801,plain,(
    ! [A_21614,B_21615,E_21616,F_21617] :
      ( k4_relset_1(A_21614,B_21615,'#skF_3','#skF_4',E_21616,F_21617) = k5_relat_1(E_21616,F_21617)
      | ~ m1_subset_1(F_21617,k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1(E_21616,k1_zfmisc_1(k2_zfmisc_1(A_21614,B_21615))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55264,c_56547])).

tff(c_60106,plain,(
    ! [A_21795,B_21796,E_21797] :
      ( k4_relset_1(A_21795,B_21796,'#skF_3','#skF_4',E_21797,'#skF_4') = k5_relat_1(E_21797,'#skF_4')
      | ~ m1_subset_1(E_21797,k1_zfmisc_1(k2_zfmisc_1(A_21795,B_21796))) ) ),
    inference(resolution,[status(thm)],[c_56711,c_56801])).

tff(c_65800,plain,(
    ! [A_21990,B_21991] : k4_relset_1(A_21990,B_21991,'#skF_3','#skF_4','#skF_4','#skF_4') = k5_relat_1('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_55876,c_60106])).

tff(c_56712,plain,(
    ! [A_21613] : m1_subset_1(A_21613,k1_zfmisc_1(A_21613)) ),
    inference(splitRight,[status(thm)],[c_56541])).

tff(c_56858,plain,(
    ! [B_21623,A_21624] :
      ( v1_xboole_0(k2_zfmisc_1(B_21623,A_21624))
      | ~ v1_xboole_0(A_21624) ) ),
    inference(resolution,[status(thm)],[c_56712,c_4])).

tff(c_56938,plain,(
    ! [B_21631,A_21632] :
      ( k2_zfmisc_1(B_21631,A_21632) = '#skF_4'
      | ~ v1_xboole_0(A_21632) ) ),
    inference(resolution,[status(thm)],[c_56858,c_39996])).

tff(c_56950,plain,(
    ! [B_21631] : k2_zfmisc_1(B_21631,'#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_39994,c_56938])).

tff(c_56882,plain,(
    ! [F_21628,B_21627,A_21626,C_21625,D_21629,E_21630] :
      ( m1_subset_1(k4_relset_1(A_21626,B_21627,C_21625,D_21629,E_21630,F_21628),k1_zfmisc_1(k2_zfmisc_1(A_21626,D_21629)))
      | ~ m1_subset_1(F_21628,k1_zfmisc_1(k2_zfmisc_1(C_21625,D_21629)))
      | ~ m1_subset_1(E_21630,k1_zfmisc_1(k2_zfmisc_1(A_21626,B_21627))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_56925,plain,(
    ! [B_21627,C_21625,E_21630,F_21628] :
      ( m1_subset_1(k4_relset_1('#skF_3',B_21627,C_21625,'#skF_4',E_21630,F_21628),k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1(F_21628,k1_zfmisc_1(k2_zfmisc_1(C_21625,'#skF_4')))
      | ~ m1_subset_1(E_21630,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_21627))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55264,c_56882])).

tff(c_57090,plain,(
    ! [B_21627,C_21625,E_21630,F_21628] :
      ( m1_subset_1(k4_relset_1('#skF_3',B_21627,C_21625,'#skF_4',E_21630,F_21628),k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1(F_21628,k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1(E_21630,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_21627))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56950,c_56925])).

tff(c_65806,plain,(
    ! [B_21991] :
      ( m1_subset_1(k5_relat_1('#skF_4','#skF_4'),k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_21991))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65800,c_57090])).

tff(c_65814,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55876,c_55876,c_65806])).

tff(c_65871,plain,(
    v1_xboole_0(k5_relat_1('#skF_4','#skF_4')) ),
    inference(resolution,[status(thm)],[c_65814,c_55323])).

tff(c_65913,plain,(
    k5_relat_1('#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_65871,c_39996])).

tff(c_8,plain,(
    ! [C_10,A_8] :
      ( k1_xboole_0 = C_10
      | ~ v1_funct_2(C_10,A_8,k1_xboole_0)
      | k1_xboole_0 = A_8
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_55740,plain,(
    ! [C_20431,A_20432] :
      ( C_20431 = '#skF_4'
      | ~ v1_funct_2(C_20431,A_20432,'#skF_4')
      | A_20432 = '#skF_4'
      | ~ m1_subset_1(C_20431,k1_zfmisc_1(k2_zfmisc_1(A_20432,'#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39993,c_39993,c_39993,c_39993,c_8])).

tff(c_55757,plain,(
    ! [C_20431] :
      ( C_20431 = '#skF_4'
      | ~ v1_funct_2(C_20431,'#skF_3','#skF_4')
      | '#skF_3' = '#skF_4'
      | ~ m1_subset_1(C_20431,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55264,c_55740])).

tff(c_55777,plain,(
    ! [C_20431] :
      ( C_20431 = '#skF_4'
      | ~ v1_funct_2(C_20431,'#skF_3','#skF_4')
      | ~ m1_subset_1(C_20431,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48261,c_55757])).

tff(c_65869,plain,
    ( k5_relat_1('#skF_4','#skF_4') = '#skF_4'
    | ~ v1_funct_2(k5_relat_1('#skF_4','#skF_4'),'#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_65814,c_55777])).

tff(c_65876,plain,(
    ~ v1_funct_2(k5_relat_1('#skF_4','#skF_4'),'#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_65869])).

tff(c_65936,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_55466,c_65913,c_65876])).

tff(c_65937,plain,(
    k5_relat_1('#skF_4','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_65869])).

tff(c_50495,plain,(
    ! [C_14330,B_14331,A_14332] :
      ( v1_xboole_0(C_14330)
      | ~ m1_subset_1(C_14330,k1_zfmisc_1(k2_zfmisc_1(B_14331,A_14332)))
      | ~ v1_xboole_0(A_14332) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_50653,plain,(
    ! [A_14342,B_14343] :
      ( v1_xboole_0('#skF_2'(A_14342,B_14343))
      | ~ v1_xboole_0(B_14343) ) ),
    inference(resolution,[status(thm)],[c_38,c_50495])).

tff(c_50685,plain,(
    ! [A_14344,B_14345] :
      ( '#skF_2'(A_14344,B_14345) = '#skF_4'
      | ~ v1_xboole_0(B_14345) ) ),
    inference(resolution,[status(thm)],[c_50653,c_39996])).

tff(c_50694,plain,(
    ! [A_14346] : '#skF_2'(A_14346,'#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_39994,c_50685])).

tff(c_50708,plain,(
    ! [A_14346] : v1_funct_2('#skF_4',A_14346,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_50694,c_28])).

tff(c_50819,plain,(
    ! [A_14353,B_14354,C_14355] :
      ( k1_relset_1(A_14353,B_14354,C_14355) = k1_relat_1(C_14355)
      | ~ m1_subset_1(C_14355,k1_zfmisc_1(k2_zfmisc_1(A_14353,B_14354))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_50838,plain,(
    ! [A_25,B_26] : k1_relset_1(A_25,B_26,'#skF_2'(A_25,B_26)) = k1_relat_1('#skF_2'(A_25,B_26)) ),
    inference(resolution,[status(thm)],[c_38,c_50819])).

tff(c_52123,plain,(
    ! [B_14442,A_14443,C_14444] :
      ( B_14442 = '#skF_4'
      | k1_relset_1(A_14443,B_14442,C_14444) = A_14443
      | ~ v1_funct_2(C_14444,A_14443,B_14442)
      | ~ m1_subset_1(C_14444,k1_zfmisc_1(k2_zfmisc_1(A_14443,B_14442))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39993,c_16])).

tff(c_52145,plain,(
    ! [B_26,A_25] :
      ( B_26 = '#skF_4'
      | k1_relset_1(A_25,B_26,'#skF_2'(A_25,B_26)) = A_25
      | ~ v1_funct_2('#skF_2'(A_25,B_26),A_25,B_26) ) ),
    inference(resolution,[status(thm)],[c_38,c_52123])).

tff(c_52167,plain,(
    ! [B_14445,A_14446] :
      ( B_14445 = '#skF_4'
      | k1_relat_1('#skF_2'(A_14446,B_14445)) = A_14446 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_50838,c_52145])).

tff(c_51743,plain,(
    ! [A_14416,B_14417] : k1_relset_1(A_14416,B_14417,'#skF_2'(A_14416,B_14417)) = k1_relat_1('#skF_2'(A_14416,B_14417)) ),
    inference(resolution,[status(thm)],[c_38,c_50819])).

tff(c_51753,plain,(
    ! [A_14416,B_14417] :
      ( m1_subset_1(k1_relat_1('#skF_2'(A_14416,B_14417)),k1_zfmisc_1(A_14416))
      | ~ m1_subset_1('#skF_2'(A_14416,B_14417),k1_zfmisc_1(k2_zfmisc_1(A_14416,B_14417))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_51743,c_18])).

tff(c_51768,plain,(
    ! [A_14416,B_14417] : m1_subset_1(k1_relat_1('#skF_2'(A_14416,B_14417)),k1_zfmisc_1(A_14416)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_51753])).

tff(c_52191,plain,(
    ! [A_14446,B_14445] :
      ( m1_subset_1(A_14446,k1_zfmisc_1(A_14446))
      | B_14445 = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52167,c_51768])).

tff(c_52479,plain,(
    ! [B_15838] : B_15838 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_52191])).

tff(c_48391,plain,(
    ! [C_11819,B_11820,A_11821] :
      ( v1_xboole_0(C_11819)
      | ~ m1_subset_1(C_11819,k1_zfmisc_1(k2_zfmisc_1(B_11820,A_11821)))
      | ~ v1_xboole_0(A_11821) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_48535,plain,(
    ! [A_11826,B_11827] :
      ( v1_xboole_0('#skF_2'(A_11826,B_11827))
      | ~ v1_xboole_0(B_11827) ) ),
    inference(resolution,[status(thm)],[c_38,c_48391])).

tff(c_48573,plain,(
    ! [A_11828,B_11829] :
      ( '#skF_2'(A_11828,B_11829) = '#skF_4'
      | ~ v1_xboole_0(B_11829) ) ),
    inference(resolution,[status(thm)],[c_48535,c_39996])).

tff(c_48580,plain,(
    ! [A_11830] : '#skF_2'(A_11830,'#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_39994,c_48573])).

tff(c_48597,plain,(
    ! [A_11830] : v1_funct_2('#skF_4',A_11830,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_48580,c_28])).

tff(c_49261,plain,(
    ! [B_11875,A_11876,C_11877] :
      ( B_11875 = '#skF_4'
      | k1_relset_1(A_11876,B_11875,C_11877) = A_11876
      | ~ v1_funct_2(C_11877,A_11876,B_11875)
      | ~ m1_subset_1(C_11877,k1_zfmisc_1(k2_zfmisc_1(A_11876,B_11875))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39993,c_16])).

tff(c_49276,plain,(
    ! [B_26,A_25] :
      ( B_26 = '#skF_4'
      | k1_relset_1(A_25,B_26,'#skF_2'(A_25,B_26)) = A_25
      | ~ v1_funct_2('#skF_2'(A_25,B_26),A_25,B_26) ) ),
    inference(resolution,[status(thm)],[c_38,c_49261])).

tff(c_50100,plain,(
    ! [B_13121,A_13122] :
      ( B_13121 = '#skF_4'
      | k1_relset_1(A_13122,B_13121,'#skF_2'(A_13122,B_13121)) = A_13122 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_49276])).

tff(c_50110,plain,(
    ! [A_13122,B_13121] :
      ( m1_subset_1(A_13122,k1_zfmisc_1(A_13122))
      | ~ m1_subset_1('#skF_2'(A_13122,B_13121),k1_zfmisc_1(k2_zfmisc_1(A_13122,B_13121)))
      | B_13121 = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50100,c_18])).

tff(c_50126,plain,(
    ! [A_13122,B_13121] :
      ( m1_subset_1(A_13122,k1_zfmisc_1(A_13122))
      | B_13121 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_50110])).

tff(c_50133,plain,(
    ! [B_13123] : B_13123 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_50126])).

tff(c_48404,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_48391])).

tff(c_48416,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_39994,c_48404])).

tff(c_48454,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_48416,c_39996])).

tff(c_48401,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_48279,c_48391])).

tff(c_48413,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_39994,c_48401])).

tff(c_48424,plain,(
    '#skF_7' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_48413,c_39996])).

tff(c_48456,plain,(
    ~ v1_funct_2(k4_relset_1('#skF_3','#skF_4','#skF_4','#skF_4','#skF_6','#skF_4'),'#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48424,c_48320])).

tff(c_48751,plain,(
    ~ v1_funct_2(k4_relset_1('#skF_3','#skF_4','#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48454,c_48456])).

tff(c_50196,plain,(
    ~ v1_funct_2('#skF_4','#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_50133,c_48751])).

tff(c_50287,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48597,c_50196])).

tff(c_50289,plain,(
    ! [A_14312] : m1_subset_1(A_14312,k1_zfmisc_1(A_14312)) ),
    inference(splitRight,[status(thm)],[c_50126])).

tff(c_50438,plain,(
    ! [B_14327,A_14328] :
      ( v1_xboole_0(k2_zfmisc_1(B_14327,A_14328))
      | ~ v1_xboole_0(A_14328) ) ),
    inference(resolution,[status(thm)],[c_50289,c_4])).

tff(c_48374,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_48371])).

tff(c_50445,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_50438,c_48374])).

tff(c_50459,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_39994,c_50445])).

tff(c_50462,plain,(
    ! [A_14329] : ~ r2_hidden(A_14329,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_48371])).

tff(c_50467,plain,(
    ! [A_40] :
      ( v1_xboole_0('#skF_6')
      | ~ m1_subset_1(A_40,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_46,c_50462])).

tff(c_50574,plain,(
    ! [A_14336] : ~ m1_subset_1(A_14336,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_50467])).

tff(c_50579,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_26,c_50574])).

tff(c_50580,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_50467])).

tff(c_50587,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_50580,c_39996])).

tff(c_50508,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_48279,c_50495])).

tff(c_50519,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_39994,c_50508])).

tff(c_50527,plain,(
    '#skF_7' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_50519,c_39996])).

tff(c_50529,plain,(
    ~ v1_funct_2(k4_relset_1('#skF_3','#skF_4','#skF_4','#skF_4','#skF_6','#skF_4'),'#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50527,c_48320])).

tff(c_50763,plain,(
    ~ v1_funct_2(k4_relset_1('#skF_3','#skF_4','#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50587,c_50529])).

tff(c_52587,plain,(
    ~ v1_funct_2('#skF_4','#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_52479,c_50763])).

tff(c_52664,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50708,c_52587])).

tff(c_52666,plain,(
    ! [A_17291] : m1_subset_1(A_17291,k1_zfmisc_1(A_17291)) ),
    inference(splitRight,[status(thm)],[c_52191])).

tff(c_52803,plain,(
    ! [B_17300,A_17301] :
      ( v1_xboole_0(k2_zfmisc_1(B_17300,A_17301))
      | ~ v1_xboole_0(A_17301) ) ),
    inference(resolution,[status(thm)],[c_52666,c_4])).

tff(c_48370,plain,(
    ! [A_11810] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_4'))
      | ~ r2_hidden(A_11810,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_48279,c_48356])).

tff(c_48373,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_48370])).

tff(c_52810,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_52803,c_48373])).

tff(c_52824,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_39994,c_52810])).

tff(c_52826,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_48370])).

tff(c_55204,plain,(
    k2_zfmisc_1('#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_52826,c_39996])).

tff(c_66657,plain,(
    ! [A_22008,B_22009,E_22010,F_22011] :
      ( k4_relset_1(A_22008,B_22009,'#skF_4','#skF_4',E_22010,F_22011) = k5_relat_1(E_22010,F_22011)
      | ~ m1_subset_1(F_22011,k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1(E_22010,k1_zfmisc_1(k2_zfmisc_1(A_22008,B_22009))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55204,c_56547])).

tff(c_126267,plain,(
    ! [A_39597,B_39598,E_39599] :
      ( k4_relset_1(A_39597,B_39598,'#skF_4','#skF_4',E_39599,'#skF_4') = k5_relat_1(E_39599,'#skF_4')
      | ~ m1_subset_1(E_39599,k1_zfmisc_1(k2_zfmisc_1(A_39597,B_39598))) ) ),
    inference(resolution,[status(thm)],[c_56711,c_66657])).

tff(c_126387,plain,(
    ! [A_39597,B_39598] : k4_relset_1(A_39597,B_39598,'#skF_4','#skF_4','#skF_4','#skF_4') = k5_relat_1('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_55876,c_126267])).

tff(c_126424,plain,(
    ! [A_39597,B_39598] : k4_relset_1(A_39597,B_39598,'#skF_4','#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_65937,c_126387])).

tff(c_126431,plain,(
    ~ v1_funct_2('#skF_4','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126424,c_55439])).

tff(c_126434,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_55466,c_126431])).

%------------------------------------------------------------------------------
