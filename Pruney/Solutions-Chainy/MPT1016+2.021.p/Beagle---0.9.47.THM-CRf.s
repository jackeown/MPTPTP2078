%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:43 EST 2020

% Result     : Theorem 3.29s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 310 expanded)
%              Number of leaves         :   35 ( 119 expanded)
%              Depth                    :   15
%              Number of atoms          :  225 (1011 expanded)
%              Number of equality atoms :   50 ( 231 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_107,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( v2_funct_1(B)
        <=> ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A)
                & k1_funct_1(B,C) = k1_funct_1(B,D) )
             => C = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_funct_2)).

tff(f_49,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
      <=> ! [B,C] :
            ( ( r2_hidden(B,k1_relat_1(A))
              & r2_hidden(C,k1_relat_1(A))
              & k1_funct_1(A,B) = k1_funct_1(A,C) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

tff(f_89,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(D)
          & r2_hidden(C,A) )
       => ( B = k1_xboole_0
          | k1_funct_1(k2_funct_1(D),k1_funct_1(D,C)) = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_536,plain,(
    ! [A_132,B_133] :
      ( ~ r2_hidden('#skF_1'(A_132,B_133),B_133)
      | r1_tarski(A_132,B_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_541,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_536])).

tff(c_40,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_38,plain,(
    v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_16,plain,(
    ! [A_12,B_13] : v1_relat_1(k2_zfmisc_1(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_66,plain,(
    ! [B_43,A_44] :
      ( v1_relat_1(B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_44))
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_69,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_4')) ),
    inference(resolution,[status(thm)],[c_36,c_66])).

tff(c_72,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_69])).

tff(c_118,plain,(
    ! [C_60,A_61,B_62] :
      ( v4_relat_1(C_60,A_61)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_122,plain,(
    v4_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_118])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k1_relat_1(B_11),A_10)
      | ~ v4_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_42,plain,
    ( '#skF_7' != '#skF_6'
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_62,plain,(
    ~ v2_funct_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_143,plain,(
    ! [A_68] :
      ( r2_hidden('#skF_3'(A_68),k1_relat_1(A_68))
      | v2_funct_1(A_68)
      | ~ v1_funct_1(A_68)
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_149,plain,(
    ! [A_68,B_2] :
      ( r2_hidden('#skF_3'(A_68),B_2)
      | ~ r1_tarski(k1_relat_1(A_68),B_2)
      | v2_funct_1(A_68)
      | ~ v1_funct_1(A_68)
      | ~ v1_relat_1(A_68) ) ),
    inference(resolution,[status(thm)],[c_143,c_2])).

tff(c_128,plain,(
    ! [A_66] :
      ( '#skF_2'(A_66) != '#skF_3'(A_66)
      | v2_funct_1(A_66)
      | ~ v1_funct_1(A_66)
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_131,plain,
    ( '#skF_2'('#skF_5') != '#skF_3'('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_128,c_62])).

tff(c_134,plain,(
    '#skF_2'('#skF_5') != '#skF_3'('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_40,c_131])).

tff(c_135,plain,(
    ! [A_67] :
      ( r2_hidden('#skF_2'(A_67),k1_relat_1(A_67))
      | v2_funct_1(A_67)
      | ~ v1_funct_1(A_67)
      | ~ v1_relat_1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_141,plain,(
    ! [A_67,B_2] :
      ( r2_hidden('#skF_2'(A_67),B_2)
      | ~ r1_tarski(k1_relat_1(A_67),B_2)
      | v2_funct_1(A_67)
      | ~ v1_funct_1(A_67)
      | ~ v1_relat_1(A_67) ) ),
    inference(resolution,[status(thm)],[c_135,c_2])).

tff(c_177,plain,(
    ! [A_75] :
      ( k1_funct_1(A_75,'#skF_2'(A_75)) = k1_funct_1(A_75,'#skF_3'(A_75))
      | v2_funct_1(A_75)
      | ~ v1_funct_1(A_75)
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_60,plain,(
    ! [D_35,C_34] :
      ( v2_funct_1('#skF_5')
      | D_35 = C_34
      | k1_funct_1('#skF_5',D_35) != k1_funct_1('#skF_5',C_34)
      | ~ r2_hidden(D_35,'#skF_4')
      | ~ r2_hidden(C_34,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_101,plain,(
    ! [D_35,C_34] :
      ( D_35 = C_34
      | k1_funct_1('#skF_5',D_35) != k1_funct_1('#skF_5',C_34)
      | ~ r2_hidden(D_35,'#skF_4')
      | ~ r2_hidden(C_34,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_60])).

tff(c_186,plain,(
    ! [D_35] :
      ( D_35 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',D_35) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden(D_35,'#skF_4')
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4')
      | v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_101])).

tff(c_195,plain,(
    ! [D_35] :
      ( D_35 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',D_35) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden(D_35,'#skF_4')
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4')
      | v2_funct_1('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_40,c_186])).

tff(c_196,plain,(
    ! [D_35] :
      ( D_35 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',D_35) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden(D_35,'#skF_4')
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_195])).

tff(c_389,plain,(
    ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_196])).

tff(c_392,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_4')
    | v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_141,c_389])).

tff(c_395,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_4')
    | v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_40,c_392])).

tff(c_396,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_395])).

tff(c_402,plain,
    ( ~ v4_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_14,c_396])).

tff(c_409,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_122,c_402])).

tff(c_411,plain,(
    r2_hidden('#skF_2'('#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_183,plain,(
    ! [C_34] :
      ( C_34 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',C_34) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4')
      | ~ r2_hidden(C_34,'#skF_4')
      | v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_101])).

tff(c_192,plain,(
    ! [C_34] :
      ( C_34 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',C_34) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4')
      | ~ r2_hidden(C_34,'#skF_4')
      | v2_funct_1('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_40,c_183])).

tff(c_193,plain,(
    ! [C_34] :
      ( C_34 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',C_34) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4')
      | ~ r2_hidden(C_34,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_192])).

tff(c_475,plain,(
    ! [C_34] :
      ( C_34 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',C_34) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden(C_34,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_411,c_193])).

tff(c_478,plain,
    ( '#skF_2'('#skF_5') = '#skF_3'('#skF_5')
    | ~ r2_hidden('#skF_3'('#skF_5'),'#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_475])).

tff(c_479,plain,(
    ~ r2_hidden('#skF_3'('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_478])).

tff(c_491,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_4')
    | v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_149,c_479])).

tff(c_494,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_4')
    | v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_40,c_491])).

tff(c_495,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_494])).

tff(c_501,plain,
    ( ~ v4_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_14,c_495])).

tff(c_508,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_122,c_501])).

tff(c_510,plain,(
    v2_funct_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_48,plain,
    ( r2_hidden('#skF_6','#skF_4')
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_515,plain,(
    r2_hidden('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_510,c_48])).

tff(c_910,plain,(
    ! [D_213,C_214,B_215,A_216] :
      ( k1_funct_1(k2_funct_1(D_213),k1_funct_1(D_213,C_214)) = C_214
      | k1_xboole_0 = B_215
      | ~ r2_hidden(C_214,A_216)
      | ~ v2_funct_1(D_213)
      | ~ m1_subset_1(D_213,k1_zfmisc_1(k2_zfmisc_1(A_216,B_215)))
      | ~ v1_funct_2(D_213,A_216,B_215)
      | ~ v1_funct_1(D_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_961,plain,(
    ! [D_222,B_223] :
      ( k1_funct_1(k2_funct_1(D_222),k1_funct_1(D_222,'#skF_6')) = '#skF_6'
      | k1_xboole_0 = B_223
      | ~ v2_funct_1(D_222)
      | ~ m1_subset_1(D_222,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_223)))
      | ~ v1_funct_2(D_222,'#skF_4',B_223)
      | ~ v1_funct_1(D_222) ) ),
    inference(resolution,[status(thm)],[c_515,c_910])).

tff(c_963,plain,
    ( k1_funct_1(k2_funct_1('#skF_5'),k1_funct_1('#skF_5','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_4'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_2('#skF_5','#skF_4','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_961])).

tff(c_966,plain,
    ( k1_funct_1(k2_funct_1('#skF_5'),k1_funct_1('#skF_5','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_510,c_963])).

tff(c_967,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_966])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_558,plain,(
    ! [C_139,B_140,A_141] :
      ( r2_hidden(C_139,B_140)
      | ~ r2_hidden(C_139,A_141)
      | ~ r1_tarski(A_141,B_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_568,plain,(
    ! [B_142] :
      ( r2_hidden('#skF_6',B_142)
      | ~ r1_tarski('#skF_4',B_142) ) ),
    inference(resolution,[status(thm)],[c_515,c_558])).

tff(c_28,plain,(
    ! [B_22,A_21] :
      ( ~ r1_tarski(B_22,A_21)
      | ~ r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_584,plain,(
    ! [B_144] :
      ( ~ r1_tarski(B_144,'#skF_6')
      | ~ r1_tarski('#skF_4',B_144) ) ),
    inference(resolution,[status(thm)],[c_568,c_28])).

tff(c_592,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_584])).

tff(c_979,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_967,c_592])).

tff(c_983,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_541,c_979])).

tff(c_985,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_966])).

tff(c_509,plain,(
    '#skF_7' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_984,plain,(
    k1_funct_1(k2_funct_1('#skF_5'),k1_funct_1('#skF_5','#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_966])).

tff(c_44,plain,
    ( k1_funct_1('#skF_5','#skF_7') = k1_funct_1('#skF_5','#skF_6')
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_517,plain,(
    k1_funct_1('#skF_5','#skF_7') = k1_funct_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_510,c_44])).

tff(c_46,plain,
    ( r2_hidden('#skF_7','#skF_4')
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_513,plain,(
    r2_hidden('#skF_7','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_510,c_46])).

tff(c_999,plain,(
    ! [D_226,B_227] :
      ( k1_funct_1(k2_funct_1(D_226),k1_funct_1(D_226,'#skF_7')) = '#skF_7'
      | k1_xboole_0 = B_227
      | ~ v2_funct_1(D_226)
      | ~ m1_subset_1(D_226,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_227)))
      | ~ v1_funct_2(D_226,'#skF_4',B_227)
      | ~ v1_funct_1(D_226) ) ),
    inference(resolution,[status(thm)],[c_513,c_910])).

tff(c_1001,plain,
    ( k1_funct_1(k2_funct_1('#skF_5'),k1_funct_1('#skF_5','#skF_7')) = '#skF_7'
    | k1_xboole_0 = '#skF_4'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_2('#skF_5','#skF_4','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_999])).

tff(c_1004,plain,
    ( '#skF_7' = '#skF_6'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_510,c_984,c_517,c_1001])).

tff(c_1006,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_985,c_509,c_1004])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:04:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.29/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.51  
% 3.29/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.51  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 3.29/1.51  
% 3.29/1.51  %Foreground sorts:
% 3.29/1.51  
% 3.29/1.51  
% 3.29/1.51  %Background operators:
% 3.29/1.51  
% 3.29/1.51  
% 3.29/1.51  %Foreground operators:
% 3.29/1.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.29/1.51  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.29/1.51  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.29/1.51  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.29/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.29/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.29/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.29/1.51  tff('#skF_7', type, '#skF_7': $i).
% 3.29/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.29/1.51  tff('#skF_5', type, '#skF_5': $i).
% 3.29/1.51  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.29/1.51  tff('#skF_6', type, '#skF_6': $i).
% 3.29/1.51  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.29/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.29/1.51  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.29/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.29/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.29/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.29/1.51  tff('#skF_4', type, '#skF_4': $i).
% 3.29/1.51  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.29/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.29/1.51  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.29/1.51  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.29/1.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.29/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.29/1.51  
% 3.29/1.53  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.29/1.53  tff(f_107, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) <=> (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_funct_2)).
% 3.29/1.53  tff(f_49, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.29/1.53  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.29/1.53  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.29/1.53  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.29/1.53  tff(f_64, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_funct_1)).
% 3.29/1.53  tff(f_89, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(D) & r2_hidden(C, A)) => ((B = k1_xboole_0) | (k1_funct_1(k2_funct_1(D), k1_funct_1(D, C)) = C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_funct_2)).
% 3.29/1.53  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.29/1.53  tff(f_69, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.29/1.53  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.29/1.53  tff(c_536, plain, (![A_132, B_133]: (~r2_hidden('#skF_1'(A_132, B_133), B_133) | r1_tarski(A_132, B_133))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.29/1.53  tff(c_541, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_536])).
% 3.29/1.53  tff(c_40, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.29/1.53  tff(c_38, plain, (v1_funct_2('#skF_5', '#skF_4', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.29/1.53  tff(c_16, plain, (![A_12, B_13]: (v1_relat_1(k2_zfmisc_1(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.29/1.53  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.29/1.53  tff(c_66, plain, (![B_43, A_44]: (v1_relat_1(B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(A_44)) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.29/1.53  tff(c_69, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_36, c_66])).
% 3.29/1.53  tff(c_72, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_69])).
% 3.29/1.53  tff(c_118, plain, (![C_60, A_61, B_62]: (v4_relat_1(C_60, A_61) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.29/1.53  tff(c_122, plain, (v4_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_36, c_118])).
% 3.29/1.53  tff(c_14, plain, (![B_11, A_10]: (r1_tarski(k1_relat_1(B_11), A_10) | ~v4_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.29/1.53  tff(c_42, plain, ('#skF_7'!='#skF_6' | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.29/1.53  tff(c_62, plain, (~v2_funct_1('#skF_5')), inference(splitLeft, [status(thm)], [c_42])).
% 3.29/1.53  tff(c_143, plain, (![A_68]: (r2_hidden('#skF_3'(A_68), k1_relat_1(A_68)) | v2_funct_1(A_68) | ~v1_funct_1(A_68) | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.29/1.53  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.29/1.53  tff(c_149, plain, (![A_68, B_2]: (r2_hidden('#skF_3'(A_68), B_2) | ~r1_tarski(k1_relat_1(A_68), B_2) | v2_funct_1(A_68) | ~v1_funct_1(A_68) | ~v1_relat_1(A_68))), inference(resolution, [status(thm)], [c_143, c_2])).
% 3.29/1.53  tff(c_128, plain, (![A_66]: ('#skF_2'(A_66)!='#skF_3'(A_66) | v2_funct_1(A_66) | ~v1_funct_1(A_66) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.29/1.53  tff(c_131, plain, ('#skF_2'('#skF_5')!='#skF_3'('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_128, c_62])).
% 3.29/1.53  tff(c_134, plain, ('#skF_2'('#skF_5')!='#skF_3'('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_40, c_131])).
% 3.29/1.53  tff(c_135, plain, (![A_67]: (r2_hidden('#skF_2'(A_67), k1_relat_1(A_67)) | v2_funct_1(A_67) | ~v1_funct_1(A_67) | ~v1_relat_1(A_67))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.29/1.53  tff(c_141, plain, (![A_67, B_2]: (r2_hidden('#skF_2'(A_67), B_2) | ~r1_tarski(k1_relat_1(A_67), B_2) | v2_funct_1(A_67) | ~v1_funct_1(A_67) | ~v1_relat_1(A_67))), inference(resolution, [status(thm)], [c_135, c_2])).
% 3.29/1.53  tff(c_177, plain, (![A_75]: (k1_funct_1(A_75, '#skF_2'(A_75))=k1_funct_1(A_75, '#skF_3'(A_75)) | v2_funct_1(A_75) | ~v1_funct_1(A_75) | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.29/1.53  tff(c_60, plain, (![D_35, C_34]: (v2_funct_1('#skF_5') | D_35=C_34 | k1_funct_1('#skF_5', D_35)!=k1_funct_1('#skF_5', C_34) | ~r2_hidden(D_35, '#skF_4') | ~r2_hidden(C_34, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.29/1.53  tff(c_101, plain, (![D_35, C_34]: (D_35=C_34 | k1_funct_1('#skF_5', D_35)!=k1_funct_1('#skF_5', C_34) | ~r2_hidden(D_35, '#skF_4') | ~r2_hidden(C_34, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_62, c_60])).
% 3.29/1.53  tff(c_186, plain, (![D_35]: (D_35='#skF_2'('#skF_5') | k1_funct_1('#skF_5', D_35)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden(D_35, '#skF_4') | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4') | v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_177, c_101])).
% 3.29/1.53  tff(c_195, plain, (![D_35]: (D_35='#skF_2'('#skF_5') | k1_funct_1('#skF_5', D_35)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden(D_35, '#skF_4') | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4') | v2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_40, c_186])).
% 3.29/1.53  tff(c_196, plain, (![D_35]: (D_35='#skF_2'('#skF_5') | k1_funct_1('#skF_5', D_35)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden(D_35, '#skF_4') | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_62, c_195])).
% 3.29/1.53  tff(c_389, plain, (~r2_hidden('#skF_2'('#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_196])).
% 3.29/1.53  tff(c_392, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_4') | v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_141, c_389])).
% 3.29/1.53  tff(c_395, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_4') | v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_40, c_392])).
% 3.29/1.53  tff(c_396, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_62, c_395])).
% 3.29/1.53  tff(c_402, plain, (~v4_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_14, c_396])).
% 3.29/1.53  tff(c_409, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_122, c_402])).
% 3.29/1.53  tff(c_411, plain, (r2_hidden('#skF_2'('#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_196])).
% 3.29/1.53  tff(c_183, plain, (![C_34]: (C_34='#skF_2'('#skF_5') | k1_funct_1('#skF_5', C_34)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4') | ~r2_hidden(C_34, '#skF_4') | v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_177, c_101])).
% 3.29/1.53  tff(c_192, plain, (![C_34]: (C_34='#skF_2'('#skF_5') | k1_funct_1('#skF_5', C_34)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4') | ~r2_hidden(C_34, '#skF_4') | v2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_40, c_183])).
% 3.29/1.53  tff(c_193, plain, (![C_34]: (C_34='#skF_2'('#skF_5') | k1_funct_1('#skF_5', C_34)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4') | ~r2_hidden(C_34, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_62, c_192])).
% 3.29/1.53  tff(c_475, plain, (![C_34]: (C_34='#skF_2'('#skF_5') | k1_funct_1('#skF_5', C_34)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden(C_34, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_411, c_193])).
% 3.29/1.53  tff(c_478, plain, ('#skF_2'('#skF_5')='#skF_3'('#skF_5') | ~r2_hidden('#skF_3'('#skF_5'), '#skF_4')), inference(reflexivity, [status(thm), theory('equality')], [c_475])).
% 3.29/1.53  tff(c_479, plain, (~r2_hidden('#skF_3'('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_134, c_478])).
% 3.29/1.53  tff(c_491, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_4') | v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_149, c_479])).
% 3.29/1.53  tff(c_494, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_4') | v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_40, c_491])).
% 3.29/1.53  tff(c_495, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_62, c_494])).
% 3.29/1.53  tff(c_501, plain, (~v4_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_14, c_495])).
% 3.29/1.53  tff(c_508, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_122, c_501])).
% 3.29/1.53  tff(c_510, plain, (v2_funct_1('#skF_5')), inference(splitRight, [status(thm)], [c_42])).
% 3.29/1.53  tff(c_48, plain, (r2_hidden('#skF_6', '#skF_4') | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.29/1.53  tff(c_515, plain, (r2_hidden('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_510, c_48])).
% 3.29/1.53  tff(c_910, plain, (![D_213, C_214, B_215, A_216]: (k1_funct_1(k2_funct_1(D_213), k1_funct_1(D_213, C_214))=C_214 | k1_xboole_0=B_215 | ~r2_hidden(C_214, A_216) | ~v2_funct_1(D_213) | ~m1_subset_1(D_213, k1_zfmisc_1(k2_zfmisc_1(A_216, B_215))) | ~v1_funct_2(D_213, A_216, B_215) | ~v1_funct_1(D_213))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.29/1.53  tff(c_961, plain, (![D_222, B_223]: (k1_funct_1(k2_funct_1(D_222), k1_funct_1(D_222, '#skF_6'))='#skF_6' | k1_xboole_0=B_223 | ~v2_funct_1(D_222) | ~m1_subset_1(D_222, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_223))) | ~v1_funct_2(D_222, '#skF_4', B_223) | ~v1_funct_1(D_222))), inference(resolution, [status(thm)], [c_515, c_910])).
% 3.29/1.53  tff(c_963, plain, (k1_funct_1(k2_funct_1('#skF_5'), k1_funct_1('#skF_5', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_4' | ~v2_funct_1('#skF_5') | ~v1_funct_2('#skF_5', '#skF_4', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_36, c_961])).
% 3.29/1.53  tff(c_966, plain, (k1_funct_1(k2_funct_1('#skF_5'), k1_funct_1('#skF_5', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_510, c_963])).
% 3.29/1.53  tff(c_967, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_966])).
% 3.29/1.53  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.29/1.53  tff(c_558, plain, (![C_139, B_140, A_141]: (r2_hidden(C_139, B_140) | ~r2_hidden(C_139, A_141) | ~r1_tarski(A_141, B_140))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.29/1.53  tff(c_568, plain, (![B_142]: (r2_hidden('#skF_6', B_142) | ~r1_tarski('#skF_4', B_142))), inference(resolution, [status(thm)], [c_515, c_558])).
% 3.29/1.53  tff(c_28, plain, (![B_22, A_21]: (~r1_tarski(B_22, A_21) | ~r2_hidden(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.29/1.53  tff(c_584, plain, (![B_144]: (~r1_tarski(B_144, '#skF_6') | ~r1_tarski('#skF_4', B_144))), inference(resolution, [status(thm)], [c_568, c_28])).
% 3.29/1.53  tff(c_592, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_584])).
% 3.29/1.53  tff(c_979, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_967, c_592])).
% 3.29/1.53  tff(c_983, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_541, c_979])).
% 3.29/1.53  tff(c_985, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_966])).
% 3.29/1.53  tff(c_509, plain, ('#skF_7'!='#skF_6'), inference(splitRight, [status(thm)], [c_42])).
% 3.29/1.53  tff(c_984, plain, (k1_funct_1(k2_funct_1('#skF_5'), k1_funct_1('#skF_5', '#skF_6'))='#skF_6'), inference(splitRight, [status(thm)], [c_966])).
% 3.29/1.53  tff(c_44, plain, (k1_funct_1('#skF_5', '#skF_7')=k1_funct_1('#skF_5', '#skF_6') | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.29/1.53  tff(c_517, plain, (k1_funct_1('#skF_5', '#skF_7')=k1_funct_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_510, c_44])).
% 3.29/1.53  tff(c_46, plain, (r2_hidden('#skF_7', '#skF_4') | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.29/1.53  tff(c_513, plain, (r2_hidden('#skF_7', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_510, c_46])).
% 3.29/1.53  tff(c_999, plain, (![D_226, B_227]: (k1_funct_1(k2_funct_1(D_226), k1_funct_1(D_226, '#skF_7'))='#skF_7' | k1_xboole_0=B_227 | ~v2_funct_1(D_226) | ~m1_subset_1(D_226, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_227))) | ~v1_funct_2(D_226, '#skF_4', B_227) | ~v1_funct_1(D_226))), inference(resolution, [status(thm)], [c_513, c_910])).
% 3.29/1.53  tff(c_1001, plain, (k1_funct_1(k2_funct_1('#skF_5'), k1_funct_1('#skF_5', '#skF_7'))='#skF_7' | k1_xboole_0='#skF_4' | ~v2_funct_1('#skF_5') | ~v1_funct_2('#skF_5', '#skF_4', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_36, c_999])).
% 3.29/1.53  tff(c_1004, plain, ('#skF_7'='#skF_6' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_510, c_984, c_517, c_1001])).
% 3.29/1.53  tff(c_1006, plain, $false, inference(negUnitSimplification, [status(thm)], [c_985, c_509, c_1004])).
% 3.29/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.53  
% 3.29/1.53  Inference rules
% 3.29/1.53  ----------------------
% 3.29/1.53  #Ref     : 4
% 3.29/1.53  #Sup     : 195
% 3.29/1.53  #Fact    : 0
% 3.29/1.53  #Define  : 0
% 3.29/1.53  #Split   : 4
% 3.29/1.53  #Chain   : 0
% 3.29/1.53  #Close   : 0
% 3.29/1.53  
% 3.29/1.53  Ordering : KBO
% 3.29/1.53  
% 3.29/1.53  Simplification rules
% 3.29/1.53  ----------------------
% 3.29/1.53  #Subsume      : 56
% 3.29/1.53  #Demod        : 65
% 3.29/1.53  #Tautology    : 33
% 3.29/1.53  #SimpNegUnit  : 8
% 3.29/1.53  #BackRed      : 13
% 3.29/1.53  
% 3.29/1.53  #Partial instantiations: 0
% 3.29/1.53  #Strategies tried      : 1
% 3.29/1.53  
% 3.29/1.53  Timing (in seconds)
% 3.29/1.53  ----------------------
% 3.29/1.53  Preprocessing        : 0.32
% 3.29/1.54  Parsing              : 0.17
% 3.29/1.54  CNF conversion       : 0.02
% 3.29/1.54  Main loop            : 0.44
% 3.29/1.54  Inferencing          : 0.17
% 3.29/1.54  Reduction            : 0.12
% 3.29/1.54  Demodulation         : 0.08
% 3.29/1.54  BG Simplification    : 0.02
% 3.29/1.54  Subsumption          : 0.09
% 3.29/1.54  Abstraction          : 0.02
% 3.29/1.54  MUC search           : 0.00
% 3.29/1.54  Cooper               : 0.00
% 3.29/1.54  Total                : 0.80
% 3.29/1.54  Index Insertion      : 0.00
% 3.29/1.54  Index Deletion       : 0.00
% 3.29/1.54  Index Matching       : 0.00
% 3.29/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
