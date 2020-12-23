%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:55 EST 2020

% Result     : Theorem 2.56s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 374 expanded)
%              Number of leaves         :   31 ( 131 expanded)
%              Depth                    :   12
%              Number of atoms          :  174 (1272 expanded)
%              Number of equality atoms :   34 ( 376 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(f_38,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

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

tff(f_50,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_40,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_140,plain,(
    ! [A_48,B_49,C_50,D_51] :
      ( r2_relset_1(A_48,B_49,C_50,C_50)
      | ~ m1_subset_1(D_51,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49)))
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_154,plain,(
    ! [C_52] :
      ( r2_relset_1('#skF_3','#skF_4',C_52,C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_40,c_140])).

tff(c_160,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_154])).

tff(c_10,plain,(
    v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_61,plain,(
    ! [A_30] :
      ( k1_xboole_0 = A_30
      | ~ v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_65,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_10,c_61])).

tff(c_36,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_67,plain,(
    '#skF_2' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_60])).

tff(c_50,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_48,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_171,plain,(
    ! [C_56,A_57,B_58] :
      ( v1_partfun1(C_56,A_57)
      | ~ v1_funct_2(C_56,A_57,B_58)
      | ~ v1_funct_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58)))
      | v1_xboole_0(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_174,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_171])).

tff(c_186,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_174])).

tff(c_192,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_186])).

tff(c_8,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_66,plain,(
    ! [A_6] :
      ( A_6 = '#skF_2'
      | ~ v1_xboole_0(A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_8])).

tff(c_195,plain,(
    '#skF_2' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_192,c_66])).

tff(c_199,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_195])).

tff(c_200,plain,(
    v1_partfun1('#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_201,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_44,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_42,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_180,plain,
    ( v1_partfun1('#skF_6','#skF_3')
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_171])).

tff(c_190,plain,
    ( v1_partfun1('#skF_6','#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_180])).

tff(c_202,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_190])).

tff(c_203,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_201,c_202])).

tff(c_204,plain,(
    v1_partfun1('#skF_6','#skF_3') ),
    inference(splitRight,[status(thm)],[c_190])).

tff(c_38,plain,(
    r1_partfun1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_206,plain,(
    ! [D_60,C_61,A_62,B_63] :
      ( D_60 = C_61
      | ~ r1_partfun1(C_61,D_60)
      | ~ v1_partfun1(D_60,A_62)
      | ~ v1_partfun1(C_61,A_62)
      | ~ m1_subset_1(D_60,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63)))
      | ~ v1_funct_1(D_60)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63)))
      | ~ v1_funct_1(C_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_208,plain,(
    ! [A_62,B_63] :
      ( '#skF_5' = '#skF_6'
      | ~ v1_partfun1('#skF_6',A_62)
      | ~ v1_partfun1('#skF_5',A_62)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_62,B_63)))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_62,B_63)))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_38,c_206])).

tff(c_211,plain,(
    ! [A_62,B_63] :
      ( '#skF_5' = '#skF_6'
      | ~ v1_partfun1('#skF_6',A_62)
      | ~ v1_partfun1('#skF_5',A_62)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_62,B_63)))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_44,c_208])).

tff(c_217,plain,(
    ! [A_68,B_69] :
      ( ~ v1_partfun1('#skF_6',A_68)
      | ~ v1_partfun1('#skF_5',A_68)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_68,B_69)))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(splitLeft,[status(thm)],[c_211])).

tff(c_220,plain,
    ( ~ v1_partfun1('#skF_6','#skF_3')
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_46,c_217])).

tff(c_230,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_200,c_204,c_220])).

tff(c_231,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_34,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_235,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_34])).

tff(c_244,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_235])).

tff(c_246,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_245,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_252,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_245])).

tff(c_20,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_247,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_245,c_245,c_20])).

tff(c_280,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_252,c_247])).

tff(c_304,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_252,c_40])).

tff(c_22,plain,(
    ! [B_10] : k2_zfmisc_1(k1_xboole_0,B_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_288,plain,(
    ! [B_10] : k2_zfmisc_1('#skF_4',B_10) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_246,c_22])).

tff(c_447,plain,(
    ! [A_102,B_103,C_104,D_105] :
      ( r2_relset_1(A_102,B_103,C_104,C_104)
      | ~ m1_subset_1(D_105,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103)))
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_449,plain,(
    ! [B_10,C_104,D_105] :
      ( r2_relset_1('#skF_4',B_10,C_104,C_104)
      | ~ m1_subset_1(D_105,k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_10))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_288,c_447])).

tff(c_452,plain,(
    ! [B_10,C_104,D_105] :
      ( r2_relset_1('#skF_4',B_10,C_104,C_104)
      | ~ m1_subset_1(D_105,k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1(C_104,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_288,c_449])).

tff(c_454,plain,(
    ! [D_105] : ~ m1_subset_1(D_105,k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_452])).

tff(c_456,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_454,c_304])).

tff(c_458,plain,(
    ! [B_106,C_107] :
      ( r2_relset_1('#skF_4',B_106,C_107,C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_452])).

tff(c_461,plain,(
    ! [B_106] : r2_relset_1('#skF_4',B_106,'#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_304,c_458])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_264,plain,(
    ! [A_70] :
      ( A_70 = '#skF_4'
      | ~ v1_xboole_0(A_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_8])).

tff(c_268,plain,(
    '#skF_2' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_10,c_264])).

tff(c_269,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_10])).

tff(c_333,plain,(
    ! [C_81,B_82,A_83] :
      ( ~ v1_xboole_0(C_81)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(C_81))
      | ~ r2_hidden(A_83,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_337,plain,(
    ! [A_83] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_83,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_304,c_333])).

tff(c_350,plain,(
    ! [A_85] : ~ r2_hidden(A_85,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_337])).

tff(c_355,plain,(
    ! [B_2] : r1_tarski('#skF_6',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_350])).

tff(c_305,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_252,c_46])).

tff(c_335,plain,(
    ! [A_83] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_83,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_305,c_333])).

tff(c_344,plain,(
    ! [A_84] : ~ r2_hidden(A_84,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_335])).

tff(c_356,plain,(
    ! [B_86] : r1_tarski('#skF_5',B_86) ),
    inference(resolution,[status(thm)],[c_6,c_344])).

tff(c_12,plain,(
    ! [B_8,A_7] :
      ( B_8 = A_7
      | ~ r1_tarski(B_8,A_7)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_368,plain,(
    ! [B_91] :
      ( B_91 = '#skF_5'
      | ~ r1_tarski(B_91,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_356,c_12])).

tff(c_381,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_355,c_368])).

tff(c_279,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_34])).

tff(c_391,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_381,c_279])).

tff(c_464,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_461,c_391])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:39:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.56/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.34  
% 2.56/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.34  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.56/1.34  
% 2.56/1.34  %Foreground sorts:
% 2.56/1.34  
% 2.56/1.34  
% 2.56/1.34  %Background operators:
% 2.56/1.34  
% 2.56/1.34  
% 2.56/1.34  %Foreground operators:
% 2.56/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.56/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.56/1.34  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.56/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.56/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.56/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.56/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.56/1.34  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.56/1.34  tff('#skF_6', type, '#skF_6': $i).
% 2.56/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.56/1.34  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.56/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.56/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.56/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.56/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.56/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.56/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.56/1.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.56/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.56/1.34  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 2.56/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.56/1.34  
% 2.56/1.36  tff(f_117, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_relset_1(A, B, C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_2)).
% 2.56/1.36  tff(f_63, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.56/1.36  tff(f_38, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_xboole_0)).
% 2.56/1.36  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.56/1.36  tff(f_77, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.56/1.36  tff(f_94, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_partfun1)).
% 2.56/1.36  tff(f_50, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.56/1.36  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.56/1.36  tff(f_57, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.56/1.36  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.56/1.36  tff(c_40, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.56/1.36  tff(c_140, plain, (![A_48, B_49, C_50, D_51]: (r2_relset_1(A_48, B_49, C_50, C_50) | ~m1_subset_1(D_51, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.56/1.36  tff(c_154, plain, (![C_52]: (r2_relset_1('#skF_3', '#skF_4', C_52, C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))))), inference(resolution, [status(thm)], [c_40, c_140])).
% 2.56/1.36  tff(c_160, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_40, c_154])).
% 2.56/1.36  tff(c_10, plain, (v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.56/1.36  tff(c_61, plain, (![A_30]: (k1_xboole_0=A_30 | ~v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.56/1.36  tff(c_65, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_10, c_61])).
% 2.56/1.36  tff(c_36, plain, (k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.56/1.36  tff(c_60, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_36])).
% 2.56/1.36  tff(c_67, plain, ('#skF_2'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_65, c_60])).
% 2.56/1.36  tff(c_50, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.56/1.36  tff(c_48, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.56/1.36  tff(c_46, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.56/1.36  tff(c_171, plain, (![C_56, A_57, B_58]: (v1_partfun1(C_56, A_57) | ~v1_funct_2(C_56, A_57, B_58) | ~v1_funct_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))) | v1_xboole_0(B_58))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.56/1.36  tff(c_174, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_46, c_171])).
% 2.56/1.36  tff(c_186, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_174])).
% 2.56/1.36  tff(c_192, plain, (v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_186])).
% 2.56/1.36  tff(c_8, plain, (![A_6]: (k1_xboole_0=A_6 | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.56/1.36  tff(c_66, plain, (![A_6]: (A_6='#skF_2' | ~v1_xboole_0(A_6))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_8])).
% 2.56/1.36  tff(c_195, plain, ('#skF_2'='#skF_4'), inference(resolution, [status(thm)], [c_192, c_66])).
% 2.56/1.36  tff(c_199, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67, c_195])).
% 2.56/1.36  tff(c_200, plain, (v1_partfun1('#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_186])).
% 2.56/1.36  tff(c_201, plain, (~v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_186])).
% 2.56/1.36  tff(c_44, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.56/1.36  tff(c_42, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.56/1.36  tff(c_180, plain, (v1_partfun1('#skF_6', '#skF_3') | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_40, c_171])).
% 2.56/1.36  tff(c_190, plain, (v1_partfun1('#skF_6', '#skF_3') | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_180])).
% 2.56/1.36  tff(c_202, plain, (v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_190])).
% 2.56/1.36  tff(c_203, plain, $false, inference(negUnitSimplification, [status(thm)], [c_201, c_202])).
% 2.56/1.36  tff(c_204, plain, (v1_partfun1('#skF_6', '#skF_3')), inference(splitRight, [status(thm)], [c_190])).
% 2.56/1.36  tff(c_38, plain, (r1_partfun1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.56/1.36  tff(c_206, plain, (![D_60, C_61, A_62, B_63]: (D_60=C_61 | ~r1_partfun1(C_61, D_60) | ~v1_partfun1(D_60, A_62) | ~v1_partfun1(C_61, A_62) | ~m1_subset_1(D_60, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))) | ~v1_funct_1(D_60) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))) | ~v1_funct_1(C_61))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.56/1.36  tff(c_208, plain, (![A_62, B_63]: ('#skF_5'='#skF_6' | ~v1_partfun1('#skF_6', A_62) | ~v1_partfun1('#skF_5', A_62) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_38, c_206])).
% 2.56/1.36  tff(c_211, plain, (![A_62, B_63]: ('#skF_5'='#skF_6' | ~v1_partfun1('#skF_6', A_62) | ~v1_partfun1('#skF_5', A_62) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_44, c_208])).
% 2.56/1.36  tff(c_217, plain, (![A_68, B_69]: (~v1_partfun1('#skF_6', A_68) | ~v1_partfun1('#skF_5', A_68) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(splitLeft, [status(thm)], [c_211])).
% 2.56/1.36  tff(c_220, plain, (~v1_partfun1('#skF_6', '#skF_3') | ~v1_partfun1('#skF_5', '#skF_3') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_46, c_217])).
% 2.56/1.36  tff(c_230, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_200, c_204, c_220])).
% 2.56/1.36  tff(c_231, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_211])).
% 2.56/1.36  tff(c_34, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.56/1.36  tff(c_235, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_231, c_34])).
% 2.56/1.36  tff(c_244, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_160, c_235])).
% 2.56/1.36  tff(c_246, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_36])).
% 2.56/1.36  tff(c_245, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_36])).
% 2.56/1.36  tff(c_252, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_246, c_245])).
% 2.56/1.36  tff(c_20, plain, (![A_9]: (k2_zfmisc_1(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.56/1.36  tff(c_247, plain, (![A_9]: (k2_zfmisc_1(A_9, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_245, c_245, c_20])).
% 2.56/1.36  tff(c_280, plain, (![A_9]: (k2_zfmisc_1(A_9, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_252, c_252, c_247])).
% 2.56/1.36  tff(c_304, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_280, c_252, c_40])).
% 2.56/1.36  tff(c_22, plain, (![B_10]: (k2_zfmisc_1(k1_xboole_0, B_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.56/1.36  tff(c_288, plain, (![B_10]: (k2_zfmisc_1('#skF_4', B_10)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_246, c_246, c_22])).
% 2.56/1.36  tff(c_447, plain, (![A_102, B_103, C_104, D_105]: (r2_relset_1(A_102, B_103, C_104, C_104) | ~m1_subset_1(D_105, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.56/1.36  tff(c_449, plain, (![B_10, C_104, D_105]: (r2_relset_1('#skF_4', B_10, C_104, C_104) | ~m1_subset_1(D_105, k1_zfmisc_1('#skF_4')) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_10))))), inference(superposition, [status(thm), theory('equality')], [c_288, c_447])).
% 2.56/1.36  tff(c_452, plain, (![B_10, C_104, D_105]: (r2_relset_1('#skF_4', B_10, C_104, C_104) | ~m1_subset_1(D_105, k1_zfmisc_1('#skF_4')) | ~m1_subset_1(C_104, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_288, c_449])).
% 2.56/1.36  tff(c_454, plain, (![D_105]: (~m1_subset_1(D_105, k1_zfmisc_1('#skF_4')))), inference(splitLeft, [status(thm)], [c_452])).
% 2.56/1.36  tff(c_456, plain, $false, inference(negUnitSimplification, [status(thm)], [c_454, c_304])).
% 2.56/1.36  tff(c_458, plain, (![B_106, C_107]: (r2_relset_1('#skF_4', B_106, C_107, C_107) | ~m1_subset_1(C_107, k1_zfmisc_1('#skF_4')))), inference(splitRight, [status(thm)], [c_452])).
% 2.56/1.36  tff(c_461, plain, (![B_106]: (r2_relset_1('#skF_4', B_106, '#skF_6', '#skF_6'))), inference(resolution, [status(thm)], [c_304, c_458])).
% 2.56/1.36  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.56/1.36  tff(c_264, plain, (![A_70]: (A_70='#skF_4' | ~v1_xboole_0(A_70))), inference(demodulation, [status(thm), theory('equality')], [c_246, c_8])).
% 2.56/1.36  tff(c_268, plain, ('#skF_2'='#skF_4'), inference(resolution, [status(thm)], [c_10, c_264])).
% 2.56/1.36  tff(c_269, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_268, c_10])).
% 2.56/1.36  tff(c_333, plain, (![C_81, B_82, A_83]: (~v1_xboole_0(C_81) | ~m1_subset_1(B_82, k1_zfmisc_1(C_81)) | ~r2_hidden(A_83, B_82))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.56/1.36  tff(c_337, plain, (![A_83]: (~v1_xboole_0('#skF_4') | ~r2_hidden(A_83, '#skF_6'))), inference(resolution, [status(thm)], [c_304, c_333])).
% 2.56/1.36  tff(c_350, plain, (![A_85]: (~r2_hidden(A_85, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_269, c_337])).
% 2.56/1.36  tff(c_355, plain, (![B_2]: (r1_tarski('#skF_6', B_2))), inference(resolution, [status(thm)], [c_6, c_350])).
% 2.56/1.36  tff(c_305, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_280, c_252, c_46])).
% 2.56/1.36  tff(c_335, plain, (![A_83]: (~v1_xboole_0('#skF_4') | ~r2_hidden(A_83, '#skF_5'))), inference(resolution, [status(thm)], [c_305, c_333])).
% 2.56/1.36  tff(c_344, plain, (![A_84]: (~r2_hidden(A_84, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_269, c_335])).
% 2.56/1.36  tff(c_356, plain, (![B_86]: (r1_tarski('#skF_5', B_86))), inference(resolution, [status(thm)], [c_6, c_344])).
% 2.56/1.36  tff(c_12, plain, (![B_8, A_7]: (B_8=A_7 | ~r1_tarski(B_8, A_7) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.56/1.36  tff(c_368, plain, (![B_91]: (B_91='#skF_5' | ~r1_tarski(B_91, '#skF_5'))), inference(resolution, [status(thm)], [c_356, c_12])).
% 2.56/1.36  tff(c_381, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_355, c_368])).
% 2.56/1.36  tff(c_279, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_252, c_34])).
% 2.56/1.36  tff(c_391, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_381, c_279])).
% 2.56/1.36  tff(c_464, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_461, c_391])).
% 2.56/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.36  
% 2.56/1.36  Inference rules
% 2.56/1.36  ----------------------
% 2.56/1.36  #Ref     : 0
% 2.56/1.36  #Sup     : 81
% 2.56/1.36  #Fact    : 0
% 2.56/1.36  #Define  : 0
% 2.56/1.36  #Split   : 7
% 2.56/1.36  #Chain   : 0
% 2.56/1.36  #Close   : 0
% 2.56/1.36  
% 2.56/1.36  Ordering : KBO
% 2.56/1.36  
% 2.56/1.36  Simplification rules
% 2.56/1.36  ----------------------
% 2.56/1.36  #Subsume      : 10
% 2.56/1.36  #Demod        : 77
% 2.56/1.36  #Tautology    : 54
% 2.56/1.36  #SimpNegUnit  : 3
% 2.56/1.36  #BackRed      : 25
% 2.56/1.36  
% 2.56/1.36  #Partial instantiations: 0
% 2.56/1.36  #Strategies tried      : 1
% 2.56/1.36  
% 2.56/1.36  Timing (in seconds)
% 2.56/1.36  ----------------------
% 2.56/1.37  Preprocessing        : 0.32
% 2.56/1.37  Parsing              : 0.17
% 2.56/1.37  CNF conversion       : 0.02
% 2.56/1.37  Main loop            : 0.27
% 2.56/1.37  Inferencing          : 0.10
% 2.56/1.37  Reduction            : 0.09
% 2.56/1.37  Demodulation         : 0.06
% 2.56/1.37  BG Simplification    : 0.02
% 2.56/1.37  Subsumption          : 0.04
% 2.56/1.37  Abstraction          : 0.01
% 2.56/1.37  MUC search           : 0.00
% 2.56/1.37  Cooper               : 0.00
% 2.56/1.37  Total                : 0.64
% 2.56/1.37  Index Insertion      : 0.00
% 2.56/1.37  Index Deletion       : 0.00
% 2.56/1.37  Index Matching       : 0.00
% 2.56/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
