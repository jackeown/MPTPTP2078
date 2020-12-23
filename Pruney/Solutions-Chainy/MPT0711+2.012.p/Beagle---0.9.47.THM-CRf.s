%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:31 EST 2020

% Result     : Theorem 8.73s
% Output     : CNFRefutation 8.85s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 252 expanded)
%              Number of leaves         :   24 ( 101 expanded)
%              Depth                    :   13
%              Number of atoms          :  148 ( 770 expanded)
%              Number of equality atoms :   48 ( 299 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ! [C] :
                ( ( k1_relat_1(A) = k1_relat_1(B)
                  & ! [D] :
                      ( r2_hidden(D,C)
                     => k1_funct_1(A,D) = k1_funct_1(B,D) ) )
               => k7_relat_1(A,C) = k7_relat_1(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_funct_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ! [C] :
              ( ( r1_tarski(C,k1_relat_1(A))
                & r1_tarski(C,k1_relat_1(B)) )
             => ( k7_relat_1(A,C) = k7_relat_1(B,C)
              <=> ! [D] :
                    ( r2_hidden(D,C)
                   => k1_funct_1(A,D) = k1_funct_1(B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t165_funct_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

tff(c_24,plain,(
    k7_relat_1('#skF_2','#skF_4') != k7_relat_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_36,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_34,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_32,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_30,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_28,plain,(
    k1_relat_1('#skF_2') = k1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_104,plain,(
    ! [B_56,A_57] :
      ( k3_xboole_0(k1_relat_1(B_56),A_57) = k1_relat_1(k7_relat_1(B_56,A_57))
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_113,plain,(
    ! [A_57] :
      ( k3_xboole_0(k1_relat_1('#skF_3'),A_57) = k1_relat_1(k7_relat_1('#skF_2',A_57))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_104])).

tff(c_127,plain,(
    ! [A_61] : k3_xboole_0(k1_relat_1('#skF_3'),A_61) = k1_relat_1(k7_relat_1('#skF_2',A_61)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_113])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( k3_xboole_0(k1_relat_1(B_12),A_11) = k1_relat_1(k7_relat_1(B_12,A_11))
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_133,plain,(
    ! [A_61] :
      ( k1_relat_1(k7_relat_1('#skF_2',A_61)) = k1_relat_1(k7_relat_1('#skF_3',A_61))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_14])).

tff(c_143,plain,(
    ! [A_61] : k1_relat_1(k7_relat_1('#skF_2',A_61)) = k1_relat_1(k7_relat_1('#skF_3',A_61)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_133])).

tff(c_69,plain,(
    ! [B_52,A_53] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_52,A_53)),k1_relat_1(B_52))
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_78,plain,(
    ! [A_53] :
      ( r1_tarski(k1_relat_1(k7_relat_1('#skF_2',A_53)),k1_relat_1('#skF_3'))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_69])).

tff(c_82,plain,(
    ! [A_53] : r1_tarski(k1_relat_1(k7_relat_1('#skF_2',A_53)),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_78])).

tff(c_148,plain,(
    ! [A_53] : r1_tarski(k1_relat_1(k7_relat_1('#skF_3',A_53)),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_82])).

tff(c_117,plain,(
    ! [A_57] : k3_xboole_0(k1_relat_1('#skF_3'),A_57) = k1_relat_1(k7_relat_1('#skF_2',A_57)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_113])).

tff(c_147,plain,(
    ! [A_57] : k3_xboole_0(k1_relat_1('#skF_3'),A_57) = k1_relat_1(k7_relat_1('#skF_3',A_57)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_117])).

tff(c_16,plain,(
    ! [A_13] :
      ( k7_relat_1(A_13,k1_relat_1(A_13)) = A_13
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_306,plain,(
    ! [C_72,A_73,B_74] :
      ( k7_relat_1(k7_relat_1(C_72,A_73),B_74) = k7_relat_1(C_72,k3_xboole_0(A_73,B_74))
      | ~ v1_relat_1(C_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_502,plain,(
    ! [A_79,B_80] :
      ( k7_relat_1(A_79,k3_xboole_0(k1_relat_1(A_79),B_80)) = k7_relat_1(A_79,B_80)
      | ~ v1_relat_1(A_79)
      | ~ v1_relat_1(A_79) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_306])).

tff(c_573,plain,(
    ! [A_57] :
      ( k7_relat_1('#skF_3',k1_relat_1(k7_relat_1('#skF_3',A_57))) = k7_relat_1('#skF_3',A_57)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_502])).

tff(c_603,plain,(
    ! [A_57] : k7_relat_1('#skF_3',k1_relat_1(k7_relat_1('#skF_3',A_57))) = k7_relat_1('#skF_3',A_57) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_32,c_573])).

tff(c_41,plain,(
    ! [A_48] :
      ( k7_relat_1(A_48,k1_relat_1(A_48)) = A_48
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_50,plain,
    ( k7_relat_1('#skF_2',k1_relat_1('#skF_3')) = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_41])).

tff(c_54,plain,(
    k7_relat_1('#skF_2',k1_relat_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_50])).

tff(c_334,plain,(
    ! [B_74] :
      ( k7_relat_1('#skF_2',k3_xboole_0(k1_relat_1('#skF_3'),B_74)) = k7_relat_1('#skF_2',B_74)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_306])).

tff(c_345,plain,(
    ! [B_74] : k7_relat_1('#skF_2',k1_relat_1(k7_relat_1('#skF_3',B_74))) = k7_relat_1('#skF_2',B_74) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_147,c_334])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_10,A_9)),k1_relat_1(B_10))
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1266,plain,(
    ! [A_103,B_104,C_105] :
      ( r2_hidden('#skF_1'(A_103,B_104,C_105),C_105)
      | k7_relat_1(B_104,C_105) = k7_relat_1(A_103,C_105)
      | ~ r1_tarski(C_105,k1_relat_1(B_104))
      | ~ r1_tarski(C_105,k1_relat_1(A_103))
      | ~ v1_funct_1(B_104)
      | ~ v1_relat_1(B_104)
      | ~ v1_funct_1(A_103)
      | ~ v1_relat_1(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_10,plain,(
    ! [A_6,B_7,C_8] :
      ( r2_hidden(A_6,B_7)
      | ~ r2_hidden(A_6,k1_relat_1(k7_relat_1(C_8,B_7)))
      | ~ v1_relat_1(C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6513,plain,(
    ! [A_208,B_209,C_210,B_211] :
      ( r2_hidden('#skF_1'(A_208,B_209,k1_relat_1(k7_relat_1(C_210,B_211))),B_211)
      | ~ v1_relat_1(C_210)
      | k7_relat_1(B_209,k1_relat_1(k7_relat_1(C_210,B_211))) = k7_relat_1(A_208,k1_relat_1(k7_relat_1(C_210,B_211)))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(C_210,B_211)),k1_relat_1(B_209))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(C_210,B_211)),k1_relat_1(A_208))
      | ~ v1_funct_1(B_209)
      | ~ v1_relat_1(B_209)
      | ~ v1_funct_1(A_208)
      | ~ v1_relat_1(A_208) ) ),
    inference(resolution,[status(thm)],[c_1266,c_10])).

tff(c_26,plain,(
    ! [D_47] :
      ( k1_funct_1('#skF_2',D_47) = k1_funct_1('#skF_3',D_47)
      | ~ r2_hidden(D_47,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_6691,plain,(
    ! [A_212,B_213,C_214] :
      ( k1_funct_1('#skF_2','#skF_1'(A_212,B_213,k1_relat_1(k7_relat_1(C_214,'#skF_4')))) = k1_funct_1('#skF_3','#skF_1'(A_212,B_213,k1_relat_1(k7_relat_1(C_214,'#skF_4'))))
      | ~ v1_relat_1(C_214)
      | k7_relat_1(B_213,k1_relat_1(k7_relat_1(C_214,'#skF_4'))) = k7_relat_1(A_212,k1_relat_1(k7_relat_1(C_214,'#skF_4')))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(C_214,'#skF_4')),k1_relat_1(B_213))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(C_214,'#skF_4')),k1_relat_1(A_212))
      | ~ v1_funct_1(B_213)
      | ~ v1_relat_1(B_213)
      | ~ v1_funct_1(A_212)
      | ~ v1_relat_1(A_212) ) ),
    inference(resolution,[status(thm)],[c_6513,c_26])).

tff(c_7561,plain,(
    ! [A_238,B_239] :
      ( k1_funct_1('#skF_2','#skF_1'(A_238,B_239,k1_relat_1(k7_relat_1(B_239,'#skF_4')))) = k1_funct_1('#skF_3','#skF_1'(A_238,B_239,k1_relat_1(k7_relat_1(B_239,'#skF_4'))))
      | k7_relat_1(B_239,k1_relat_1(k7_relat_1(B_239,'#skF_4'))) = k7_relat_1(A_238,k1_relat_1(k7_relat_1(B_239,'#skF_4')))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(B_239,'#skF_4')),k1_relat_1(A_238))
      | ~ v1_funct_1(B_239)
      | ~ v1_funct_1(A_238)
      | ~ v1_relat_1(A_238)
      | ~ v1_relat_1(B_239) ) ),
    inference(resolution,[status(thm)],[c_12,c_6691])).

tff(c_7607,plain,(
    ! [B_239] :
      ( k1_funct_1('#skF_2','#skF_1'('#skF_2',B_239,k1_relat_1(k7_relat_1(B_239,'#skF_4')))) = k1_funct_1('#skF_3','#skF_1'('#skF_2',B_239,k1_relat_1(k7_relat_1(B_239,'#skF_4'))))
      | k7_relat_1(B_239,k1_relat_1(k7_relat_1(B_239,'#skF_4'))) = k7_relat_1('#skF_2',k1_relat_1(k7_relat_1(B_239,'#skF_4')))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(B_239,'#skF_4')),k1_relat_1('#skF_3'))
      | ~ v1_funct_1(B_239)
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | ~ v1_relat_1(B_239) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_7561])).

tff(c_7934,plain,(
    ! [B_252] :
      ( k1_funct_1('#skF_2','#skF_1'('#skF_2',B_252,k1_relat_1(k7_relat_1(B_252,'#skF_4')))) = k1_funct_1('#skF_3','#skF_1'('#skF_2',B_252,k1_relat_1(k7_relat_1(B_252,'#skF_4'))))
      | k7_relat_1(B_252,k1_relat_1(k7_relat_1(B_252,'#skF_4'))) = k7_relat_1('#skF_2',k1_relat_1(k7_relat_1(B_252,'#skF_4')))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(B_252,'#skF_4')),k1_relat_1('#skF_3'))
      | ~ v1_funct_1(B_252)
      | ~ v1_relat_1(B_252) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_7607])).

tff(c_7961,plain,
    ( k1_funct_1('#skF_2','#skF_1'('#skF_2','#skF_3',k1_relat_1(k7_relat_1('#skF_3','#skF_4')))) = k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3',k1_relat_1(k7_relat_1('#skF_3','#skF_4'))))
    | k7_relat_1('#skF_2',k1_relat_1(k7_relat_1('#skF_3','#skF_4'))) = k7_relat_1('#skF_3',k1_relat_1(k7_relat_1('#skF_3','#skF_4')))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_7934])).

tff(c_7977,plain,
    ( k1_funct_1('#skF_2','#skF_1'('#skF_2','#skF_3',k1_relat_1(k7_relat_1('#skF_3','#skF_4')))) = k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3',k1_relat_1(k7_relat_1('#skF_3','#skF_4'))))
    | k7_relat_1('#skF_2','#skF_4') = k7_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_603,c_345,c_7961])).

tff(c_7978,plain,(
    k1_funct_1('#skF_2','#skF_1'('#skF_2','#skF_3',k1_relat_1(k7_relat_1('#skF_3','#skF_4')))) = k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3',k1_relat_1(k7_relat_1('#skF_3','#skF_4')))) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_7977])).

tff(c_20,plain,(
    ! [B_26,A_14,C_32] :
      ( k1_funct_1(B_26,'#skF_1'(A_14,B_26,C_32)) != k1_funct_1(A_14,'#skF_1'(A_14,B_26,C_32))
      | k7_relat_1(B_26,C_32) = k7_relat_1(A_14,C_32)
      | ~ r1_tarski(C_32,k1_relat_1(B_26))
      | ~ r1_tarski(C_32,k1_relat_1(A_14))
      | ~ v1_funct_1(B_26)
      | ~ v1_relat_1(B_26)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_8651,plain,
    ( k7_relat_1('#skF_2',k1_relat_1(k7_relat_1('#skF_3','#skF_4'))) = k7_relat_1('#skF_3',k1_relat_1(k7_relat_1('#skF_3','#skF_4')))
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_3','#skF_4')),k1_relat_1('#skF_3'))
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_3','#skF_4')),k1_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_7978,c_20])).

tff(c_8656,plain,(
    k7_relat_1('#skF_2','#skF_4') = k7_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_30,c_148,c_28,c_148,c_603,c_345,c_8651])).

tff(c_8658,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_8656])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:14:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.73/3.08  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.73/3.08  
% 8.73/3.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.73/3.08  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 8.73/3.08  
% 8.73/3.08  %Foreground sorts:
% 8.73/3.08  
% 8.73/3.08  
% 8.73/3.08  %Background operators:
% 8.73/3.08  
% 8.73/3.08  
% 8.73/3.08  %Foreground operators:
% 8.73/3.08  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 8.73/3.08  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.73/3.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.73/3.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.73/3.08  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 8.73/3.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.73/3.08  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.73/3.08  tff('#skF_2', type, '#skF_2': $i).
% 8.73/3.08  tff('#skF_3', type, '#skF_3': $i).
% 8.73/3.08  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 8.73/3.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.73/3.08  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.73/3.08  tff('#skF_4', type, '#skF_4': $i).
% 8.73/3.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.73/3.08  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.73/3.08  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.73/3.08  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.73/3.08  
% 8.85/3.10  tff(f_92, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: (((k1_relat_1(A) = k1_relat_1(B)) & (![D]: (r2_hidden(D, C) => (k1_funct_1(A, D) = k1_funct_1(B, D))))) => (k7_relat_1(A, C) = k7_relat_1(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_funct_1)).
% 8.85/3.10  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 8.85/3.10  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t89_relat_1)).
% 8.85/3.10  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 8.85/3.10  tff(f_31, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 8.85/3.10  tff(f_72, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((r1_tarski(C, k1_relat_1(A)) & r1_tarski(C, k1_relat_1(B))) => ((k7_relat_1(A, C) = k7_relat_1(B, C)) <=> (![D]: (r2_hidden(D, C) => (k1_funct_1(A, D) = k1_funct_1(B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t165_funct_1)).
% 8.85/3.10  tff(f_39, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_relat_1)).
% 8.85/3.10  tff(c_24, plain, (k7_relat_1('#skF_2', '#skF_4')!=k7_relat_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.85/3.10  tff(c_36, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.85/3.10  tff(c_34, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.85/3.10  tff(c_32, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.85/3.10  tff(c_30, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.85/3.10  tff(c_28, plain, (k1_relat_1('#skF_2')=k1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.85/3.10  tff(c_104, plain, (![B_56, A_57]: (k3_xboole_0(k1_relat_1(B_56), A_57)=k1_relat_1(k7_relat_1(B_56, A_57)) | ~v1_relat_1(B_56))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.85/3.10  tff(c_113, plain, (![A_57]: (k3_xboole_0(k1_relat_1('#skF_3'), A_57)=k1_relat_1(k7_relat_1('#skF_2', A_57)) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_104])).
% 8.85/3.10  tff(c_127, plain, (![A_61]: (k3_xboole_0(k1_relat_1('#skF_3'), A_61)=k1_relat_1(k7_relat_1('#skF_2', A_61)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_113])).
% 8.85/3.10  tff(c_14, plain, (![B_12, A_11]: (k3_xboole_0(k1_relat_1(B_12), A_11)=k1_relat_1(k7_relat_1(B_12, A_11)) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.85/3.10  tff(c_133, plain, (![A_61]: (k1_relat_1(k7_relat_1('#skF_2', A_61))=k1_relat_1(k7_relat_1('#skF_3', A_61)) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_127, c_14])).
% 8.85/3.10  tff(c_143, plain, (![A_61]: (k1_relat_1(k7_relat_1('#skF_2', A_61))=k1_relat_1(k7_relat_1('#skF_3', A_61)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_133])).
% 8.85/3.10  tff(c_69, plain, (![B_52, A_53]: (r1_tarski(k1_relat_1(k7_relat_1(B_52, A_53)), k1_relat_1(B_52)) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.85/3.10  tff(c_78, plain, (![A_53]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_2', A_53)), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_69])).
% 8.85/3.10  tff(c_82, plain, (![A_53]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_2', A_53)), k1_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_78])).
% 8.85/3.10  tff(c_148, plain, (![A_53]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_3', A_53)), k1_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_82])).
% 8.85/3.10  tff(c_117, plain, (![A_57]: (k3_xboole_0(k1_relat_1('#skF_3'), A_57)=k1_relat_1(k7_relat_1('#skF_2', A_57)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_113])).
% 8.85/3.10  tff(c_147, plain, (![A_57]: (k3_xboole_0(k1_relat_1('#skF_3'), A_57)=k1_relat_1(k7_relat_1('#skF_3', A_57)))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_117])).
% 8.85/3.10  tff(c_16, plain, (![A_13]: (k7_relat_1(A_13, k1_relat_1(A_13))=A_13 | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.85/3.10  tff(c_306, plain, (![C_72, A_73, B_74]: (k7_relat_1(k7_relat_1(C_72, A_73), B_74)=k7_relat_1(C_72, k3_xboole_0(A_73, B_74)) | ~v1_relat_1(C_72))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.85/3.10  tff(c_502, plain, (![A_79, B_80]: (k7_relat_1(A_79, k3_xboole_0(k1_relat_1(A_79), B_80))=k7_relat_1(A_79, B_80) | ~v1_relat_1(A_79) | ~v1_relat_1(A_79))), inference(superposition, [status(thm), theory('equality')], [c_16, c_306])).
% 8.85/3.10  tff(c_573, plain, (![A_57]: (k7_relat_1('#skF_3', k1_relat_1(k7_relat_1('#skF_3', A_57)))=k7_relat_1('#skF_3', A_57) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_147, c_502])).
% 8.85/3.10  tff(c_603, plain, (![A_57]: (k7_relat_1('#skF_3', k1_relat_1(k7_relat_1('#skF_3', A_57)))=k7_relat_1('#skF_3', A_57))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_32, c_573])).
% 8.85/3.10  tff(c_41, plain, (![A_48]: (k7_relat_1(A_48, k1_relat_1(A_48))=A_48 | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.85/3.10  tff(c_50, plain, (k7_relat_1('#skF_2', k1_relat_1('#skF_3'))='#skF_2' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_28, c_41])).
% 8.85/3.10  tff(c_54, plain, (k7_relat_1('#skF_2', k1_relat_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_50])).
% 8.85/3.10  tff(c_334, plain, (![B_74]: (k7_relat_1('#skF_2', k3_xboole_0(k1_relat_1('#skF_3'), B_74))=k7_relat_1('#skF_2', B_74) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_54, c_306])).
% 8.85/3.10  tff(c_345, plain, (![B_74]: (k7_relat_1('#skF_2', k1_relat_1(k7_relat_1('#skF_3', B_74)))=k7_relat_1('#skF_2', B_74))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_147, c_334])).
% 8.85/3.10  tff(c_12, plain, (![B_10, A_9]: (r1_tarski(k1_relat_1(k7_relat_1(B_10, A_9)), k1_relat_1(B_10)) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.85/3.10  tff(c_1266, plain, (![A_103, B_104, C_105]: (r2_hidden('#skF_1'(A_103, B_104, C_105), C_105) | k7_relat_1(B_104, C_105)=k7_relat_1(A_103, C_105) | ~r1_tarski(C_105, k1_relat_1(B_104)) | ~r1_tarski(C_105, k1_relat_1(A_103)) | ~v1_funct_1(B_104) | ~v1_relat_1(B_104) | ~v1_funct_1(A_103) | ~v1_relat_1(A_103))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.85/3.10  tff(c_10, plain, (![A_6, B_7, C_8]: (r2_hidden(A_6, B_7) | ~r2_hidden(A_6, k1_relat_1(k7_relat_1(C_8, B_7))) | ~v1_relat_1(C_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.85/3.10  tff(c_6513, plain, (![A_208, B_209, C_210, B_211]: (r2_hidden('#skF_1'(A_208, B_209, k1_relat_1(k7_relat_1(C_210, B_211))), B_211) | ~v1_relat_1(C_210) | k7_relat_1(B_209, k1_relat_1(k7_relat_1(C_210, B_211)))=k7_relat_1(A_208, k1_relat_1(k7_relat_1(C_210, B_211))) | ~r1_tarski(k1_relat_1(k7_relat_1(C_210, B_211)), k1_relat_1(B_209)) | ~r1_tarski(k1_relat_1(k7_relat_1(C_210, B_211)), k1_relat_1(A_208)) | ~v1_funct_1(B_209) | ~v1_relat_1(B_209) | ~v1_funct_1(A_208) | ~v1_relat_1(A_208))), inference(resolution, [status(thm)], [c_1266, c_10])).
% 8.85/3.10  tff(c_26, plain, (![D_47]: (k1_funct_1('#skF_2', D_47)=k1_funct_1('#skF_3', D_47) | ~r2_hidden(D_47, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.85/3.10  tff(c_6691, plain, (![A_212, B_213, C_214]: (k1_funct_1('#skF_2', '#skF_1'(A_212, B_213, k1_relat_1(k7_relat_1(C_214, '#skF_4'))))=k1_funct_1('#skF_3', '#skF_1'(A_212, B_213, k1_relat_1(k7_relat_1(C_214, '#skF_4')))) | ~v1_relat_1(C_214) | k7_relat_1(B_213, k1_relat_1(k7_relat_1(C_214, '#skF_4')))=k7_relat_1(A_212, k1_relat_1(k7_relat_1(C_214, '#skF_4'))) | ~r1_tarski(k1_relat_1(k7_relat_1(C_214, '#skF_4')), k1_relat_1(B_213)) | ~r1_tarski(k1_relat_1(k7_relat_1(C_214, '#skF_4')), k1_relat_1(A_212)) | ~v1_funct_1(B_213) | ~v1_relat_1(B_213) | ~v1_funct_1(A_212) | ~v1_relat_1(A_212))), inference(resolution, [status(thm)], [c_6513, c_26])).
% 8.85/3.10  tff(c_7561, plain, (![A_238, B_239]: (k1_funct_1('#skF_2', '#skF_1'(A_238, B_239, k1_relat_1(k7_relat_1(B_239, '#skF_4'))))=k1_funct_1('#skF_3', '#skF_1'(A_238, B_239, k1_relat_1(k7_relat_1(B_239, '#skF_4')))) | k7_relat_1(B_239, k1_relat_1(k7_relat_1(B_239, '#skF_4')))=k7_relat_1(A_238, k1_relat_1(k7_relat_1(B_239, '#skF_4'))) | ~r1_tarski(k1_relat_1(k7_relat_1(B_239, '#skF_4')), k1_relat_1(A_238)) | ~v1_funct_1(B_239) | ~v1_funct_1(A_238) | ~v1_relat_1(A_238) | ~v1_relat_1(B_239))), inference(resolution, [status(thm)], [c_12, c_6691])).
% 8.85/3.10  tff(c_7607, plain, (![B_239]: (k1_funct_1('#skF_2', '#skF_1'('#skF_2', B_239, k1_relat_1(k7_relat_1(B_239, '#skF_4'))))=k1_funct_1('#skF_3', '#skF_1'('#skF_2', B_239, k1_relat_1(k7_relat_1(B_239, '#skF_4')))) | k7_relat_1(B_239, k1_relat_1(k7_relat_1(B_239, '#skF_4')))=k7_relat_1('#skF_2', k1_relat_1(k7_relat_1(B_239, '#skF_4'))) | ~r1_tarski(k1_relat_1(k7_relat_1(B_239, '#skF_4')), k1_relat_1('#skF_3')) | ~v1_funct_1(B_239) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(B_239))), inference(superposition, [status(thm), theory('equality')], [c_28, c_7561])).
% 8.85/3.10  tff(c_7934, plain, (![B_252]: (k1_funct_1('#skF_2', '#skF_1'('#skF_2', B_252, k1_relat_1(k7_relat_1(B_252, '#skF_4'))))=k1_funct_1('#skF_3', '#skF_1'('#skF_2', B_252, k1_relat_1(k7_relat_1(B_252, '#skF_4')))) | k7_relat_1(B_252, k1_relat_1(k7_relat_1(B_252, '#skF_4')))=k7_relat_1('#skF_2', k1_relat_1(k7_relat_1(B_252, '#skF_4'))) | ~r1_tarski(k1_relat_1(k7_relat_1(B_252, '#skF_4')), k1_relat_1('#skF_3')) | ~v1_funct_1(B_252) | ~v1_relat_1(B_252))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_7607])).
% 8.85/3.10  tff(c_7961, plain, (k1_funct_1('#skF_2', '#skF_1'('#skF_2', '#skF_3', k1_relat_1(k7_relat_1('#skF_3', '#skF_4'))))=k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3', k1_relat_1(k7_relat_1('#skF_3', '#skF_4')))) | k7_relat_1('#skF_2', k1_relat_1(k7_relat_1('#skF_3', '#skF_4')))=k7_relat_1('#skF_3', k1_relat_1(k7_relat_1('#skF_3', '#skF_4'))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_7934])).
% 8.85/3.10  tff(c_7977, plain, (k1_funct_1('#skF_2', '#skF_1'('#skF_2', '#skF_3', k1_relat_1(k7_relat_1('#skF_3', '#skF_4'))))=k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3', k1_relat_1(k7_relat_1('#skF_3', '#skF_4')))) | k7_relat_1('#skF_2', '#skF_4')=k7_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_603, c_345, c_7961])).
% 8.85/3.10  tff(c_7978, plain, (k1_funct_1('#skF_2', '#skF_1'('#skF_2', '#skF_3', k1_relat_1(k7_relat_1('#skF_3', '#skF_4'))))=k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3', k1_relat_1(k7_relat_1('#skF_3', '#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_24, c_7977])).
% 8.85/3.10  tff(c_20, plain, (![B_26, A_14, C_32]: (k1_funct_1(B_26, '#skF_1'(A_14, B_26, C_32))!=k1_funct_1(A_14, '#skF_1'(A_14, B_26, C_32)) | k7_relat_1(B_26, C_32)=k7_relat_1(A_14, C_32) | ~r1_tarski(C_32, k1_relat_1(B_26)) | ~r1_tarski(C_32, k1_relat_1(A_14)) | ~v1_funct_1(B_26) | ~v1_relat_1(B_26) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.85/3.10  tff(c_8651, plain, (k7_relat_1('#skF_2', k1_relat_1(k7_relat_1('#skF_3', '#skF_4')))=k7_relat_1('#skF_3', k1_relat_1(k7_relat_1('#skF_3', '#skF_4'))) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_3', '#skF_4')), k1_relat_1('#skF_3')) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_3', '#skF_4')), k1_relat_1('#skF_2')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_7978, c_20])).
% 8.85/3.10  tff(c_8656, plain, (k7_relat_1('#skF_2', '#skF_4')=k7_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_30, c_148, c_28, c_148, c_603, c_345, c_8651])).
% 8.85/3.10  tff(c_8658, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_8656])).
% 8.85/3.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.85/3.10  
% 8.85/3.10  Inference rules
% 8.85/3.10  ----------------------
% 8.85/3.10  #Ref     : 2
% 8.85/3.10  #Sup     : 1927
% 8.85/3.10  #Fact    : 0
% 8.85/3.10  #Define  : 0
% 8.85/3.10  #Split   : 1
% 8.85/3.10  #Chain   : 0
% 8.85/3.10  #Close   : 0
% 8.85/3.10  
% 8.85/3.10  Ordering : KBO
% 8.85/3.10  
% 8.85/3.10  Simplification rules
% 8.85/3.10  ----------------------
% 8.85/3.10  #Subsume      : 434
% 8.85/3.10  #Demod        : 4822
% 8.85/3.10  #Tautology    : 603
% 8.85/3.10  #SimpNegUnit  : 4
% 8.85/3.10  #BackRed      : 14
% 8.85/3.10  
% 8.85/3.10  #Partial instantiations: 0
% 8.85/3.10  #Strategies tried      : 1
% 8.85/3.10  
% 8.85/3.10  Timing (in seconds)
% 8.85/3.10  ----------------------
% 8.85/3.11  Preprocessing        : 0.32
% 8.85/3.11  Parsing              : 0.17
% 8.85/3.11  CNF conversion       : 0.03
% 8.85/3.11  Main loop            : 2.01
% 8.85/3.11  Inferencing          : 0.55
% 8.85/3.11  Reduction            : 0.90
% 8.85/3.11  Demodulation         : 0.74
% 8.85/3.11  BG Simplification    : 0.09
% 8.85/3.11  Subsumption          : 0.38
% 8.85/3.11  Abstraction          : 0.15
% 8.85/3.11  MUC search           : 0.00
% 8.85/3.11  Cooper               : 0.00
% 8.85/3.11  Total                : 2.37
% 8.85/3.11  Index Insertion      : 0.00
% 8.85/3.11  Index Deletion       : 0.00
% 8.85/3.11  Index Matching       : 0.00
% 8.85/3.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
