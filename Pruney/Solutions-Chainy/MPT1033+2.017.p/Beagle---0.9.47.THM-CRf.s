%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:52 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 409 expanded)
%              Number of leaves         :   31 ( 148 expanded)
%              Depth                    :   11
%              Number of atoms          :  172 (1268 expanded)
%              Number of equality atoms :   17 ( 169 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_125,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( r1_partfun1(C,D)
             => ( ( B = k1_xboole_0
                  & A != k1_xboole_0 )
                | r2_relset_1(A,B,C,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_2)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ( v1_partfun1(C,A)
              & v1_partfun1(D,A)
              & r1_partfun1(C,D) )
           => C = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,A,B)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ! [E] :
                ( m1_subset_1(E,A)
               => k1_funct_1(C,E) = k1_funct_1(D,E) )
           => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_funct_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_42,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_36,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_114,plain,(
    ! [C_57,B_58,A_59] :
      ( v1_xboole_0(C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(B_58,A_59)))
      | ~ v1_xboole_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_121,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_114])).

tff(c_123,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_121])).

tff(c_46,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_44,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_124,plain,(
    ! [C_60,A_61,B_62] :
      ( v1_partfun1(C_60,A_61)
      | ~ v1_funct_2(C_60,A_61,B_62)
      | ~ v1_funct_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62)))
      | v1_xboole_0(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_130,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_124])).

tff(c_137,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_130])).

tff(c_138,plain,(
    v1_partfun1('#skF_6','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_137])).

tff(c_40,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_38,plain,(
    v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_127,plain,
    ( v1_partfun1('#skF_7','#skF_4')
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_7')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_124])).

tff(c_133,plain,
    ( v1_partfun1('#skF_7','#skF_4')
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_127])).

tff(c_134,plain,(
    v1_partfun1('#skF_7','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_133])).

tff(c_34,plain,(
    r1_partfun1('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_139,plain,(
    ! [D_63,C_64,A_65,B_66] :
      ( D_63 = C_64
      | ~ r1_partfun1(C_64,D_63)
      | ~ v1_partfun1(D_63,A_65)
      | ~ v1_partfun1(C_64,A_65)
      | ~ m1_subset_1(D_63,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66)))
      | ~ v1_funct_1(D_63)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66)))
      | ~ v1_funct_1(C_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_141,plain,(
    ! [A_65,B_66] :
      ( '#skF_7' = '#skF_6'
      | ~ v1_partfun1('#skF_7',A_65)
      | ~ v1_partfun1('#skF_6',A_65)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(A_65,B_66)))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_65,B_66)))
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_34,c_139])).

tff(c_144,plain,(
    ! [A_65,B_66] :
      ( '#skF_7' = '#skF_6'
      | ~ v1_partfun1('#skF_7',A_65)
      | ~ v1_partfun1('#skF_6',A_65)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(A_65,B_66)))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_40,c_141])).

tff(c_191,plain,(
    ! [A_84,B_85] :
      ( ~ v1_partfun1('#skF_7',A_84)
      | ~ v1_partfun1('#skF_6',A_84)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(A_84,B_85)))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(splitLeft,[status(thm)],[c_144])).

tff(c_194,plain,
    ( ~ v1_partfun1('#skF_7','#skF_4')
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_36,c_191])).

tff(c_198,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_138,c_134,c_194])).

tff(c_199,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_30,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_202,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_30])).

tff(c_24,plain,(
    ! [D_26,A_20,B_21,C_22] :
      ( k1_funct_1(D_26,'#skF_3'(A_20,B_21,C_22,D_26)) != k1_funct_1(C_22,'#skF_3'(A_20,B_21,C_22,D_26))
      | r2_relset_1(A_20,B_21,C_22,D_26)
      | ~ m1_subset_1(D_26,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21)))
      | ~ v1_funct_2(D_26,A_20,B_21)
      | ~ v1_funct_1(D_26)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21)))
      | ~ v1_funct_2(C_22,A_20,B_21)
      | ~ v1_funct_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_238,plain,(
    ! [A_95,B_96,C_97] :
      ( r2_relset_1(A_95,B_96,C_97,C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96)))
      | ~ v1_funct_2(C_97,A_95,B_96)
      | ~ v1_funct_1(C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96)))
      | ~ v1_funct_2(C_97,A_95,B_96)
      | ~ v1_funct_1(C_97) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_24])).

tff(c_240,plain,
    ( r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_238])).

tff(c_243,plain,(
    r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_240])).

tff(c_245,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_202,c_243])).

tff(c_247,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_121])).

tff(c_122,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_114])).

tff(c_268,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_122])).

tff(c_246,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_121])).

tff(c_64,plain,(
    ! [A_42,B_43] :
      ( r2_hidden('#skF_2'(A_42,B_43),A_42)
      | r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_74,plain,(
    ! [A_42,B_43] :
      ( ~ v1_xboole_0(A_42)
      | r1_tarski(A_42,B_43) ) ),
    inference(resolution,[status(thm)],[c_64,c_2])).

tff(c_75,plain,(
    ! [A_44,B_45] :
      ( ~ v1_xboole_0(A_44)
      | r1_tarski(A_44,B_45) ) ),
    inference(resolution,[status(thm)],[c_64,c_2])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_79,plain,(
    ! [B_46,A_47] :
      ( B_46 = A_47
      | ~ r1_tarski(B_46,A_47)
      | ~ v1_xboole_0(A_47) ) ),
    inference(resolution,[status(thm)],[c_75,c_12])).

tff(c_86,plain,(
    ! [B_43,A_42] :
      ( B_43 = A_42
      | ~ v1_xboole_0(B_43)
      | ~ v1_xboole_0(A_42) ) ),
    inference(resolution,[status(thm)],[c_74,c_79])).

tff(c_273,plain,(
    ! [A_101] :
      ( A_101 = '#skF_7'
      | ~ v1_xboole_0(A_101) ) ),
    inference(resolution,[status(thm)],[c_246,c_86])).

tff(c_283,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_268,c_273])).

tff(c_284,plain,(
    '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_247,c_273])).

tff(c_302,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_284])).

tff(c_290,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_30])).

tff(c_327,plain,(
    ~ r2_relset_1('#skF_4','#skF_6','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_302,c_290])).

tff(c_306,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_302,c_44])).

tff(c_304,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_302,c_42])).

tff(c_392,plain,(
    ! [A_129,B_130,C_131] :
      ( r2_relset_1(A_129,B_130,C_131,C_131)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130)))
      | ~ v1_funct_2(C_131,A_129,B_130)
      | ~ v1_funct_1(C_131)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130)))
      | ~ v1_funct_2(C_131,A_129,B_130)
      | ~ v1_funct_1(C_131) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_24])).

tff(c_394,plain,
    ( r2_relset_1('#skF_4','#skF_6','#skF_6','#skF_6')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_6')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_6')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_304,c_392])).

tff(c_397,plain,(
    r2_relset_1('#skF_4','#skF_6','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_306,c_304,c_394])).

tff(c_399,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_327,c_397])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:07:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.33  
% 2.17/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.33  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_3
% 2.17/1.33  
% 2.17/1.33  %Foreground sorts:
% 2.17/1.33  
% 2.17/1.33  
% 2.17/1.33  %Background operators:
% 2.17/1.33  
% 2.17/1.33  
% 2.17/1.33  %Foreground operators:
% 2.17/1.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.17/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.33  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.17/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.17/1.33  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.17/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.17/1.33  tff('#skF_7', type, '#skF_7': $i).
% 2.17/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.17/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.17/1.33  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.17/1.33  tff('#skF_6', type, '#skF_6': $i).
% 2.17/1.33  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.17/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.17/1.33  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.17/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.17/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.17/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.17/1.33  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.17/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.17/1.33  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 2.17/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.17/1.33  
% 2.56/1.34  tff(f_125, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_relset_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_2)).
% 2.56/1.34  tff(f_51, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 2.56/1.34  tff(f_65, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.56/1.34  tff(f_102, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_partfun1)).
% 2.56/1.34  tff(f_85, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (m1_subset_1(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_funct_2)).
% 2.56/1.34  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.56/1.34  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.56/1.34  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.56/1.34  tff(c_42, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.56/1.34  tff(c_36, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.56/1.34  tff(c_114, plain, (![C_57, B_58, A_59]: (v1_xboole_0(C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(B_58, A_59))) | ~v1_xboole_0(A_59))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.56/1.34  tff(c_121, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_36, c_114])).
% 2.56/1.34  tff(c_123, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_121])).
% 2.56/1.34  tff(c_46, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.56/1.34  tff(c_44, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.56/1.34  tff(c_124, plain, (![C_60, A_61, B_62]: (v1_partfun1(C_60, A_61) | ~v1_funct_2(C_60, A_61, B_62) | ~v1_funct_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))) | v1_xboole_0(B_62))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.56/1.34  tff(c_130, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_42, c_124])).
% 2.56/1.34  tff(c_137, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_130])).
% 2.56/1.34  tff(c_138, plain, (v1_partfun1('#skF_6', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_123, c_137])).
% 2.56/1.34  tff(c_40, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.56/1.34  tff(c_38, plain, (v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.56/1.34  tff(c_127, plain, (v1_partfun1('#skF_7', '#skF_4') | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_7') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_36, c_124])).
% 2.56/1.34  tff(c_133, plain, (v1_partfun1('#skF_7', '#skF_4') | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_127])).
% 2.56/1.34  tff(c_134, plain, (v1_partfun1('#skF_7', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_123, c_133])).
% 2.56/1.34  tff(c_34, plain, (r1_partfun1('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.56/1.34  tff(c_139, plain, (![D_63, C_64, A_65, B_66]: (D_63=C_64 | ~r1_partfun1(C_64, D_63) | ~v1_partfun1(D_63, A_65) | ~v1_partfun1(C_64, A_65) | ~m1_subset_1(D_63, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))) | ~v1_funct_1(D_63) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))) | ~v1_funct_1(C_64))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.56/1.34  tff(c_141, plain, (![A_65, B_66]: ('#skF_7'='#skF_6' | ~v1_partfun1('#skF_7', A_65) | ~v1_partfun1('#skF_6', A_65) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))) | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_34, c_139])).
% 2.56/1.34  tff(c_144, plain, (![A_65, B_66]: ('#skF_7'='#skF_6' | ~v1_partfun1('#skF_7', A_65) | ~v1_partfun1('#skF_6', A_65) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_40, c_141])).
% 2.56/1.34  tff(c_191, plain, (![A_84, B_85]: (~v1_partfun1('#skF_7', A_84) | ~v1_partfun1('#skF_6', A_84) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(splitLeft, [status(thm)], [c_144])).
% 2.56/1.34  tff(c_194, plain, (~v1_partfun1('#skF_7', '#skF_4') | ~v1_partfun1('#skF_6', '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_36, c_191])).
% 2.56/1.34  tff(c_198, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_138, c_134, c_194])).
% 2.56/1.34  tff(c_199, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_144])).
% 2.56/1.34  tff(c_30, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.56/1.34  tff(c_202, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_199, c_30])).
% 2.56/1.34  tff(c_24, plain, (![D_26, A_20, B_21, C_22]: (k1_funct_1(D_26, '#skF_3'(A_20, B_21, C_22, D_26))!=k1_funct_1(C_22, '#skF_3'(A_20, B_21, C_22, D_26)) | r2_relset_1(A_20, B_21, C_22, D_26) | ~m1_subset_1(D_26, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))) | ~v1_funct_2(D_26, A_20, B_21) | ~v1_funct_1(D_26) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))) | ~v1_funct_2(C_22, A_20, B_21) | ~v1_funct_1(C_22))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.56/1.34  tff(c_238, plain, (![A_95, B_96, C_97]: (r2_relset_1(A_95, B_96, C_97, C_97) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))) | ~v1_funct_2(C_97, A_95, B_96) | ~v1_funct_1(C_97) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))) | ~v1_funct_2(C_97, A_95, B_96) | ~v1_funct_1(C_97))), inference(reflexivity, [status(thm), theory('equality')], [c_24])).
% 2.56/1.34  tff(c_240, plain, (r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_42, c_238])).
% 2.56/1.34  tff(c_243, plain, (r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_240])).
% 2.56/1.34  tff(c_245, plain, $false, inference(negUnitSimplification, [status(thm)], [c_202, c_243])).
% 2.56/1.34  tff(c_247, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_121])).
% 2.56/1.34  tff(c_122, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_42, c_114])).
% 2.56/1.34  tff(c_268, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_247, c_122])).
% 2.56/1.34  tff(c_246, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_121])).
% 2.56/1.34  tff(c_64, plain, (![A_42, B_43]: (r2_hidden('#skF_2'(A_42, B_43), A_42) | r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.56/1.34  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.56/1.34  tff(c_74, plain, (![A_42, B_43]: (~v1_xboole_0(A_42) | r1_tarski(A_42, B_43))), inference(resolution, [status(thm)], [c_64, c_2])).
% 2.56/1.34  tff(c_75, plain, (![A_44, B_45]: (~v1_xboole_0(A_44) | r1_tarski(A_44, B_45))), inference(resolution, [status(thm)], [c_64, c_2])).
% 2.56/1.34  tff(c_12, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.56/1.34  tff(c_79, plain, (![B_46, A_47]: (B_46=A_47 | ~r1_tarski(B_46, A_47) | ~v1_xboole_0(A_47))), inference(resolution, [status(thm)], [c_75, c_12])).
% 2.56/1.34  tff(c_86, plain, (![B_43, A_42]: (B_43=A_42 | ~v1_xboole_0(B_43) | ~v1_xboole_0(A_42))), inference(resolution, [status(thm)], [c_74, c_79])).
% 2.56/1.34  tff(c_273, plain, (![A_101]: (A_101='#skF_7' | ~v1_xboole_0(A_101))), inference(resolution, [status(thm)], [c_246, c_86])).
% 2.56/1.34  tff(c_283, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_268, c_273])).
% 2.56/1.34  tff(c_284, plain, ('#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_247, c_273])).
% 2.56/1.34  tff(c_302, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_283, c_284])).
% 2.56/1.34  tff(c_290, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_283, c_30])).
% 2.56/1.34  tff(c_327, plain, (~r2_relset_1('#skF_4', '#skF_6', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_302, c_290])).
% 2.56/1.34  tff(c_306, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_302, c_44])).
% 2.56/1.34  tff(c_304, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_302, c_42])).
% 2.56/1.34  tff(c_392, plain, (![A_129, B_130, C_131]: (r2_relset_1(A_129, B_130, C_131, C_131) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))) | ~v1_funct_2(C_131, A_129, B_130) | ~v1_funct_1(C_131) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))) | ~v1_funct_2(C_131, A_129, B_130) | ~v1_funct_1(C_131))), inference(reflexivity, [status(thm), theory('equality')], [c_24])).
% 2.56/1.34  tff(c_394, plain, (r2_relset_1('#skF_4', '#skF_6', '#skF_6', '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_6'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_6') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_304, c_392])).
% 2.56/1.34  tff(c_397, plain, (r2_relset_1('#skF_4', '#skF_6', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_306, c_304, c_394])).
% 2.56/1.34  tff(c_399, plain, $false, inference(negUnitSimplification, [status(thm)], [c_327, c_397])).
% 2.56/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.34  
% 2.56/1.34  Inference rules
% 2.56/1.34  ----------------------
% 2.56/1.34  #Ref     : 2
% 2.56/1.34  #Sup     : 64
% 2.56/1.34  #Fact    : 0
% 2.56/1.34  #Define  : 0
% 2.56/1.34  #Split   : 3
% 2.56/1.34  #Chain   : 0
% 2.56/1.34  #Close   : 0
% 2.56/1.34  
% 2.56/1.34  Ordering : KBO
% 2.56/1.34  
% 2.56/1.35  Simplification rules
% 2.56/1.35  ----------------------
% 2.56/1.35  #Subsume      : 15
% 2.56/1.35  #Demod        : 74
% 2.56/1.35  #Tautology    : 33
% 2.56/1.35  #SimpNegUnit  : 6
% 2.56/1.35  #BackRed      : 17
% 2.56/1.35  
% 2.56/1.35  #Partial instantiations: 0
% 2.56/1.35  #Strategies tried      : 1
% 2.56/1.35  
% 2.56/1.35  Timing (in seconds)
% 2.56/1.35  ----------------------
% 2.56/1.35  Preprocessing        : 0.31
% 2.56/1.35  Parsing              : 0.17
% 2.56/1.35  CNF conversion       : 0.02
% 2.56/1.35  Main loop            : 0.26
% 2.56/1.35  Inferencing          : 0.10
% 2.56/1.35  Reduction            : 0.08
% 2.56/1.35  Demodulation         : 0.06
% 2.56/1.35  BG Simplification    : 0.02
% 2.56/1.35  Subsumption          : 0.05
% 2.56/1.35  Abstraction          : 0.01
% 2.56/1.35  MUC search           : 0.00
% 2.56/1.35  Cooper               : 0.00
% 2.56/1.35  Total                : 0.61
% 2.56/1.35  Index Insertion      : 0.00
% 2.56/1.35  Index Deletion       : 0.00
% 2.56/1.35  Index Matching       : 0.00
% 2.56/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
