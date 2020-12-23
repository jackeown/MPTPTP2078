%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:54 EST 2020

% Result     : Theorem 2.93s
% Output     : CNFRefutation 3.04s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 267 expanded)
%              Number of leaves         :   29 ( 103 expanded)
%              Depth                    :   10
%              Number of atoms          :  199 ( 906 expanded)
%              Number of equality atoms :   16 ( 116 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_117,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_2)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_94,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_466,plain,(
    ! [A_142,B_143,C_144,D_145] :
      ( r2_relset_1(A_142,B_143,C_144,C_144)
      | ~ m1_subset_1(D_145,k1_zfmisc_1(k2_zfmisc_1(A_142,B_143)))
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(A_142,B_143))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_482,plain,(
    ! [C_146] :
      ( r2_relset_1('#skF_2','#skF_3',C_146,C_146)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_36,c_466])).

tff(c_499,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_482])).

tff(c_46,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_44,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_67,plain,(
    ! [C_41,B_42,A_43] :
      ( ~ v1_xboole_0(C_41)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(C_41))
      | ~ r2_hidden(A_43,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_76,plain,(
    ! [A_10,A_43] :
      ( ~ v1_xboole_0(A_10)
      | ~ r2_hidden(A_43,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_67])).

tff(c_78,plain,(
    ! [A_44] : ~ r2_hidden(A_44,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_83,plain,(
    ! [B_2] : r1_tarski(k1_xboole_0,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_78])).

tff(c_168,plain,(
    ! [A_63,B_64,C_65,D_66] :
      ( r2_relset_1(A_63,B_64,C_65,C_65)
      | ~ m1_subset_1(D_66,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64)))
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_178,plain,(
    ! [C_67] :
      ( r2_relset_1('#skF_2','#skF_3',C_67,C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_36,c_168])).

tff(c_187,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_178])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( v1_xboole_0(k2_zfmisc_1(A_8,B_9))
      | ~ v1_xboole_0(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_74,plain,(
    ! [A_43] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r2_hidden(A_43,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_36,c_67])).

tff(c_84,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_92,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_84])).

tff(c_122,plain,(
    ! [C_55,A_56,B_57] :
      ( v1_partfun1(C_55,A_56)
      | ~ v1_funct_2(C_55,A_56,B_57)
      | ~ v1_funct_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57)))
      | v1_xboole_0(B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_128,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_122])).

tff(c_139,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_128])).

tff(c_140,plain,(
    v1_partfun1('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_139])).

tff(c_40,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_38,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_125,plain,
    ( v1_partfun1('#skF_5','#skF_2')
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_122])).

tff(c_135,plain,
    ( v1_partfun1('#skF_5','#skF_2')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_125])).

tff(c_136,plain,(
    v1_partfun1('#skF_5','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_135])).

tff(c_34,plain,(
    r1_partfun1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_211,plain,(
    ! [D_77,C_78,A_79,B_80] :
      ( D_77 = C_78
      | ~ r1_partfun1(C_78,D_77)
      | ~ v1_partfun1(D_77,A_79)
      | ~ v1_partfun1(C_78,A_79)
      | ~ m1_subset_1(D_77,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80)))
      | ~ v1_funct_1(D_77)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80)))
      | ~ v1_funct_1(C_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_213,plain,(
    ! [A_79,B_80] :
      ( '#skF_5' = '#skF_4'
      | ~ v1_partfun1('#skF_5',A_79)
      | ~ v1_partfun1('#skF_4',A_79)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_79,B_80)))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_79,B_80)))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_211])).

tff(c_216,plain,(
    ! [A_79,B_80] :
      ( '#skF_5' = '#skF_4'
      | ~ v1_partfun1('#skF_5',A_79)
      | ~ v1_partfun1('#skF_4',A_79)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_79,B_80)))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_40,c_213])).

tff(c_218,plain,(
    ! [A_81,B_82] :
      ( ~ v1_partfun1('#skF_5',A_81)
      | ~ v1_partfun1('#skF_4',A_81)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_81,B_82)))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(splitLeft,[status(thm)],[c_216])).

tff(c_221,plain,
    ( ~ v1_partfun1('#skF_5','#skF_2')
    | ~ v1_partfun1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_36,c_218])).

tff(c_225,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_140,c_136,c_221])).

tff(c_226,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_216])).

tff(c_30,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_231,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_30])).

tff(c_240,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_231])).

tff(c_242,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_75,plain,(
    ! [A_43] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r2_hidden(A_43,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_42,c_67])).

tff(c_243,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_75])).

tff(c_259,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_243])).

tff(c_272,plain,(
    ! [A_90] : ~ r2_hidden(A_90,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_282,plain,(
    ! [B_92] : r1_tarski('#skF_4',B_92) ),
    inference(resolution,[status(thm)],[c_6,c_272])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_291,plain,(
    ! [B_94] :
      ( B_94 = '#skF_4'
      | ~ r1_tarski(B_94,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_282,c_8])).

tff(c_308,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_83,c_291])).

tff(c_338,plain,(
    ! [A_10] : m1_subset_1('#skF_4',k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_16])).

tff(c_394,plain,(
    ! [A_109,B_110,C_111,D_112] :
      ( r2_relset_1(A_109,B_110,C_111,C_111)
      | ~ m1_subset_1(D_112,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110)))
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_398,plain,(
    ! [A_113,B_114,C_115] :
      ( r2_relset_1(A_113,B_114,C_115,C_115)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114))) ) ),
    inference(resolution,[status(thm)],[c_338,c_394])).

tff(c_402,plain,(
    ! [A_113,B_114] : r2_relset_1(A_113,B_114,'#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_338,c_398])).

tff(c_266,plain,(
    ! [A_89] : ~ r2_hidden(A_89,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_271,plain,(
    ! [B_2] : r1_tarski('#skF_5',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_266])).

tff(c_311,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_271,c_291])).

tff(c_317,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_311,c_30])).

tff(c_405,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_402,c_317])).

tff(c_406,plain,(
    ! [A_10] : ~ v1_xboole_0(A_10) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_24,plain,(
    ! [C_24,A_21,B_22] :
      ( v1_partfun1(C_24,A_21)
      | ~ v1_funct_2(C_24,A_21,B_22)
      | ~ v1_funct_1(C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22)))
      | v1_xboole_0(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_526,plain,(
    ! [C_155,A_156,B_157] :
      ( v1_partfun1(C_155,A_156)
      | ~ v1_funct_2(C_155,A_156,B_157)
      | ~ v1_funct_1(C_155)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(A_156,B_157))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_406,c_24])).

tff(c_540,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_526])).

tff(c_552,plain,(
    v1_partfun1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_540])).

tff(c_537,plain,
    ( v1_partfun1('#skF_5','#skF_2')
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_526])).

tff(c_549,plain,(
    v1_partfun1('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_537])).

tff(c_580,plain,(
    ! [D_171,C_172,A_173,B_174] :
      ( D_171 = C_172
      | ~ r1_partfun1(C_172,D_171)
      | ~ v1_partfun1(D_171,A_173)
      | ~ v1_partfun1(C_172,A_173)
      | ~ m1_subset_1(D_171,k1_zfmisc_1(k2_zfmisc_1(A_173,B_174)))
      | ~ v1_funct_1(D_171)
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(A_173,B_174)))
      | ~ v1_funct_1(C_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_582,plain,(
    ! [A_173,B_174] :
      ( '#skF_5' = '#skF_4'
      | ~ v1_partfun1('#skF_5',A_173)
      | ~ v1_partfun1('#skF_4',A_173)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_173,B_174)))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_173,B_174)))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_580])).

tff(c_585,plain,(
    ! [A_173,B_174] :
      ( '#skF_5' = '#skF_4'
      | ~ v1_partfun1('#skF_5',A_173)
      | ~ v1_partfun1('#skF_4',A_173)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_173,B_174)))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_173,B_174))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_40,c_582])).

tff(c_593,plain,(
    ! [A_182,B_183] :
      ( ~ v1_partfun1('#skF_5',A_182)
      | ~ v1_partfun1('#skF_4',A_182)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_182,B_183)))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_182,B_183))) ) ),
    inference(splitLeft,[status(thm)],[c_585])).

tff(c_596,plain,
    ( ~ v1_partfun1('#skF_5','#skF_2')
    | ~ v1_partfun1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_36,c_593])).

tff(c_600,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_552,c_549,c_596])).

tff(c_601,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_585])).

tff(c_606,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_601,c_30])).

tff(c_615,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_499,c_606])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:34:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.93/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.93/1.47  
% 2.93/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.93/1.47  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.93/1.47  
% 2.93/1.47  %Foreground sorts:
% 2.93/1.47  
% 2.93/1.47  
% 2.93/1.47  %Background operators:
% 2.93/1.47  
% 2.93/1.47  
% 2.93/1.47  %Foreground operators:
% 2.93/1.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.93/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.93/1.47  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.93/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.93/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.93/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.93/1.47  tff('#skF_5', type, '#skF_5': $i).
% 2.93/1.47  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.93/1.47  tff('#skF_2', type, '#skF_2': $i).
% 2.93/1.47  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.93/1.47  tff('#skF_3', type, '#skF_3': $i).
% 2.93/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.93/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.93/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.93/1.47  tff('#skF_4', type, '#skF_4': $i).
% 2.93/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.93/1.47  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.93/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.93/1.47  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 2.93/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.93/1.47  
% 3.04/1.49  tff(f_117, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_relset_1(A, B, C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_2)).
% 3.04/1.49  tff(f_63, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 3.04/1.49  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.04/1.49  tff(f_44, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.04/1.49  tff(f_57, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.04/1.49  tff(f_42, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 3.04/1.49  tff(f_77, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 3.04/1.49  tff(f_94, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_partfun1)).
% 3.04/1.49  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.04/1.49  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.04/1.49  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.04/1.49  tff(c_466, plain, (![A_142, B_143, C_144, D_145]: (r2_relset_1(A_142, B_143, C_144, C_144) | ~m1_subset_1(D_145, k1_zfmisc_1(k2_zfmisc_1(A_142, B_143))) | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(A_142, B_143))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.04/1.49  tff(c_482, plain, (![C_146]: (r2_relset_1('#skF_2', '#skF_3', C_146, C_146) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))))), inference(resolution, [status(thm)], [c_36, c_466])).
% 3.04/1.49  tff(c_499, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_482])).
% 3.04/1.49  tff(c_46, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.04/1.49  tff(c_44, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.04/1.49  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.04/1.49  tff(c_16, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.04/1.49  tff(c_67, plain, (![C_41, B_42, A_43]: (~v1_xboole_0(C_41) | ~m1_subset_1(B_42, k1_zfmisc_1(C_41)) | ~r2_hidden(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.04/1.49  tff(c_76, plain, (![A_10, A_43]: (~v1_xboole_0(A_10) | ~r2_hidden(A_43, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_67])).
% 3.04/1.49  tff(c_78, plain, (![A_44]: (~r2_hidden(A_44, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_76])).
% 3.04/1.49  tff(c_83, plain, (![B_2]: (r1_tarski(k1_xboole_0, B_2))), inference(resolution, [status(thm)], [c_6, c_78])).
% 3.04/1.49  tff(c_168, plain, (![A_63, B_64, C_65, D_66]: (r2_relset_1(A_63, B_64, C_65, C_65) | ~m1_subset_1(D_66, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.04/1.49  tff(c_178, plain, (![C_67]: (r2_relset_1('#skF_2', '#skF_3', C_67, C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))))), inference(resolution, [status(thm)], [c_36, c_168])).
% 3.04/1.49  tff(c_187, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_178])).
% 3.04/1.49  tff(c_14, plain, (![A_8, B_9]: (v1_xboole_0(k2_zfmisc_1(A_8, B_9)) | ~v1_xboole_0(B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.04/1.49  tff(c_74, plain, (![A_43]: (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3')) | ~r2_hidden(A_43, '#skF_5'))), inference(resolution, [status(thm)], [c_36, c_67])).
% 3.04/1.49  tff(c_84, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_74])).
% 3.04/1.49  tff(c_92, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_14, c_84])).
% 3.04/1.49  tff(c_122, plain, (![C_55, A_56, B_57]: (v1_partfun1(C_55, A_56) | ~v1_funct_2(C_55, A_56, B_57) | ~v1_funct_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))) | v1_xboole_0(B_57))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.04/1.49  tff(c_128, plain, (v1_partfun1('#skF_4', '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_42, c_122])).
% 3.04/1.49  tff(c_139, plain, (v1_partfun1('#skF_4', '#skF_2') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_128])).
% 3.04/1.49  tff(c_140, plain, (v1_partfun1('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_92, c_139])).
% 3.04/1.49  tff(c_40, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.04/1.49  tff(c_38, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.04/1.49  tff(c_125, plain, (v1_partfun1('#skF_5', '#skF_2') | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_36, c_122])).
% 3.04/1.49  tff(c_135, plain, (v1_partfun1('#skF_5', '#skF_2') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_125])).
% 3.04/1.49  tff(c_136, plain, (v1_partfun1('#skF_5', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_92, c_135])).
% 3.04/1.49  tff(c_34, plain, (r1_partfun1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.04/1.49  tff(c_211, plain, (![D_77, C_78, A_79, B_80]: (D_77=C_78 | ~r1_partfun1(C_78, D_77) | ~v1_partfun1(D_77, A_79) | ~v1_partfun1(C_78, A_79) | ~m1_subset_1(D_77, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))) | ~v1_funct_1(D_77) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))) | ~v1_funct_1(C_78))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.04/1.49  tff(c_213, plain, (![A_79, B_80]: ('#skF_5'='#skF_4' | ~v1_partfun1('#skF_5', A_79) | ~v1_partfun1('#skF_4', A_79) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_34, c_211])).
% 3.04/1.49  tff(c_216, plain, (![A_79, B_80]: ('#skF_5'='#skF_4' | ~v1_partfun1('#skF_5', A_79) | ~v1_partfun1('#skF_4', A_79) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_40, c_213])).
% 3.04/1.49  tff(c_218, plain, (![A_81, B_82]: (~v1_partfun1('#skF_5', A_81) | ~v1_partfun1('#skF_4', A_81) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(splitLeft, [status(thm)], [c_216])).
% 3.04/1.49  tff(c_221, plain, (~v1_partfun1('#skF_5', '#skF_2') | ~v1_partfun1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_36, c_218])).
% 3.04/1.49  tff(c_225, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_140, c_136, c_221])).
% 3.04/1.49  tff(c_226, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_216])).
% 3.04/1.49  tff(c_30, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.04/1.49  tff(c_231, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_226, c_30])).
% 3.04/1.49  tff(c_240, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_187, c_231])).
% 3.04/1.49  tff(c_242, plain, (v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_74])).
% 3.04/1.49  tff(c_75, plain, (![A_43]: (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3')) | ~r2_hidden(A_43, '#skF_4'))), inference(resolution, [status(thm)], [c_42, c_67])).
% 3.04/1.49  tff(c_243, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_75])).
% 3.04/1.49  tff(c_259, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_242, c_243])).
% 3.04/1.49  tff(c_272, plain, (![A_90]: (~r2_hidden(A_90, '#skF_4'))), inference(splitRight, [status(thm)], [c_75])).
% 3.04/1.49  tff(c_282, plain, (![B_92]: (r1_tarski('#skF_4', B_92))), inference(resolution, [status(thm)], [c_6, c_272])).
% 3.04/1.49  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.04/1.49  tff(c_291, plain, (![B_94]: (B_94='#skF_4' | ~r1_tarski(B_94, '#skF_4'))), inference(resolution, [status(thm)], [c_282, c_8])).
% 3.04/1.49  tff(c_308, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_83, c_291])).
% 3.04/1.49  tff(c_338, plain, (![A_10]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_308, c_16])).
% 3.04/1.49  tff(c_394, plain, (![A_109, B_110, C_111, D_112]: (r2_relset_1(A_109, B_110, C_111, C_111) | ~m1_subset_1(D_112, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.04/1.49  tff(c_398, plain, (![A_113, B_114, C_115]: (r2_relset_1(A_113, B_114, C_115, C_115) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))))), inference(resolution, [status(thm)], [c_338, c_394])).
% 3.04/1.49  tff(c_402, plain, (![A_113, B_114]: (r2_relset_1(A_113, B_114, '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_338, c_398])).
% 3.04/1.49  tff(c_266, plain, (![A_89]: (~r2_hidden(A_89, '#skF_5'))), inference(splitRight, [status(thm)], [c_74])).
% 3.04/1.49  tff(c_271, plain, (![B_2]: (r1_tarski('#skF_5', B_2))), inference(resolution, [status(thm)], [c_6, c_266])).
% 3.04/1.49  tff(c_311, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_271, c_291])).
% 3.04/1.49  tff(c_317, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_311, c_30])).
% 3.04/1.49  tff(c_405, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_402, c_317])).
% 3.04/1.49  tff(c_406, plain, (![A_10]: (~v1_xboole_0(A_10))), inference(splitRight, [status(thm)], [c_76])).
% 3.04/1.49  tff(c_24, plain, (![C_24, A_21, B_22]: (v1_partfun1(C_24, A_21) | ~v1_funct_2(C_24, A_21, B_22) | ~v1_funct_1(C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))) | v1_xboole_0(B_22))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.04/1.49  tff(c_526, plain, (![C_155, A_156, B_157]: (v1_partfun1(C_155, A_156) | ~v1_funct_2(C_155, A_156, B_157) | ~v1_funct_1(C_155) | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(A_156, B_157))))), inference(negUnitSimplification, [status(thm)], [c_406, c_24])).
% 3.04/1.49  tff(c_540, plain, (v1_partfun1('#skF_4', '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_526])).
% 3.04/1.49  tff(c_552, plain, (v1_partfun1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_540])).
% 3.04/1.49  tff(c_537, plain, (v1_partfun1('#skF_5', '#skF_2') | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_36, c_526])).
% 3.04/1.49  tff(c_549, plain, (v1_partfun1('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_537])).
% 3.04/1.49  tff(c_580, plain, (![D_171, C_172, A_173, B_174]: (D_171=C_172 | ~r1_partfun1(C_172, D_171) | ~v1_partfun1(D_171, A_173) | ~v1_partfun1(C_172, A_173) | ~m1_subset_1(D_171, k1_zfmisc_1(k2_zfmisc_1(A_173, B_174))) | ~v1_funct_1(D_171) | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(A_173, B_174))) | ~v1_funct_1(C_172))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.04/1.49  tff(c_582, plain, (![A_173, B_174]: ('#skF_5'='#skF_4' | ~v1_partfun1('#skF_5', A_173) | ~v1_partfun1('#skF_4', A_173) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_173, B_174))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_173, B_174))) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_34, c_580])).
% 3.04/1.49  tff(c_585, plain, (![A_173, B_174]: ('#skF_5'='#skF_4' | ~v1_partfun1('#skF_5', A_173) | ~v1_partfun1('#skF_4', A_173) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_173, B_174))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_173, B_174))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_40, c_582])).
% 3.04/1.49  tff(c_593, plain, (![A_182, B_183]: (~v1_partfun1('#skF_5', A_182) | ~v1_partfun1('#skF_4', A_182) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_182, B_183))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_182, B_183))))), inference(splitLeft, [status(thm)], [c_585])).
% 3.04/1.49  tff(c_596, plain, (~v1_partfun1('#skF_5', '#skF_2') | ~v1_partfun1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_36, c_593])).
% 3.04/1.49  tff(c_600, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_552, c_549, c_596])).
% 3.04/1.49  tff(c_601, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_585])).
% 3.04/1.49  tff(c_606, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_601, c_30])).
% 3.04/1.49  tff(c_615, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_499, c_606])).
% 3.04/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.04/1.49  
% 3.04/1.49  Inference rules
% 3.04/1.49  ----------------------
% 3.04/1.49  #Ref     : 0
% 3.04/1.49  #Sup     : 106
% 3.04/1.49  #Fact    : 0
% 3.04/1.49  #Define  : 0
% 3.04/1.49  #Split   : 9
% 3.04/1.49  #Chain   : 0
% 3.04/1.49  #Close   : 0
% 3.04/1.49  
% 3.04/1.49  Ordering : KBO
% 3.04/1.49  
% 3.04/1.49  Simplification rules
% 3.04/1.49  ----------------------
% 3.04/1.49  #Subsume      : 31
% 3.04/1.49  #Demod        : 82
% 3.04/1.49  #Tautology    : 38
% 3.04/1.49  #SimpNegUnit  : 4
% 3.04/1.49  #BackRed      : 28
% 3.04/1.49  
% 3.04/1.49  #Partial instantiations: 0
% 3.04/1.49  #Strategies tried      : 1
% 3.04/1.49  
% 3.04/1.49  Timing (in seconds)
% 3.04/1.49  ----------------------
% 3.04/1.50  Preprocessing        : 0.32
% 3.04/1.50  Parsing              : 0.18
% 3.04/1.50  CNF conversion       : 0.02
% 3.04/1.50  Main loop            : 0.33
% 3.04/1.50  Inferencing          : 0.12
% 3.04/1.50  Reduction            : 0.10
% 3.04/1.50  Demodulation         : 0.07
% 3.04/1.50  BG Simplification    : 0.02
% 3.04/1.50  Subsumption          : 0.06
% 3.04/1.50  Abstraction          : 0.01
% 3.04/1.50  MUC search           : 0.00
% 3.04/1.50  Cooper               : 0.00
% 3.04/1.50  Total                : 0.69
% 3.04/1.50  Index Insertion      : 0.00
% 3.04/1.50  Index Deletion       : 0.00
% 3.04/1.50  Index Matching       : 0.00
% 3.04/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
