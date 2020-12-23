%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:56 EST 2020

% Result     : Theorem 6.78s
% Output     : CNFRefutation 6.78s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 259 expanded)
%              Number of leaves         :   32 ( 101 expanded)
%              Depth                    :   21
%              Number of atoms          :  181 ( 600 expanded)
%              Number of equality atoms :   99 ( 347 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( k1_relat_1(B) = k1_tarski(A)
         => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ~ ( A != k1_tarski(B)
        & A != k1_xboole_0
        & ! [C] :
            ~ ( r2_hidden(C,A)
              & C != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_88,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_42,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_44,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_65,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_70,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_101,plain,(
    ! [A_73] :
      ( k2_relat_1(A_73) != k1_xboole_0
      | k1_xboole_0 = A_73
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_105,plain,
    ( k2_relat_1('#skF_9') != k1_xboole_0
    | k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_70,c_101])).

tff(c_106,plain,(
    k2_relat_1('#skF_9') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_105])).

tff(c_36,plain,(
    ! [A_18,B_19] :
      ( r2_hidden('#skF_3'(A_18,B_19),A_18)
      | k1_xboole_0 = A_18
      | k1_tarski(B_19) = A_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_68,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_50,plain,(
    ! [A_22,C_58] :
      ( r2_hidden('#skF_7'(A_22,k2_relat_1(A_22),C_58),k1_relat_1(A_22))
      | ~ r2_hidden(C_58,k2_relat_1(A_22))
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_46,plain,(
    ! [A_22,D_61] :
      ( r2_hidden(k1_funct_1(A_22,D_61),k2_relat_1(A_22))
      | ~ r2_hidden(D_61,k1_relat_1(A_22))
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_4520,plain,(
    ! [A_7023,C_7024] :
      ( r2_hidden('#skF_7'(A_7023,k2_relat_1(A_7023),C_7024),k1_relat_1(A_7023))
      | ~ r2_hidden(C_7024,k2_relat_1(A_7023))
      | ~ v1_funct_1(A_7023)
      | ~ v1_relat_1(A_7023) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_66,plain,(
    k1_tarski('#skF_8') = k1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_26,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_28,plain,(
    ! [A_9,B_10] : k1_enumset1(A_9,A_9,B_10) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_159,plain,(
    ! [E_92,C_93,B_94,A_95] :
      ( E_92 = C_93
      | E_92 = B_94
      | E_92 = A_95
      | ~ r2_hidden(E_92,k1_enumset1(A_95,B_94,C_93)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_183,plain,(
    ! [E_96,B_97,A_98] :
      ( E_96 = B_97
      | E_96 = A_98
      | E_96 = A_98
      | ~ r2_hidden(E_96,k2_tarski(A_98,B_97)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_159])).

tff(c_202,plain,(
    ! [E_99,A_100] :
      ( E_99 = A_100
      | E_99 = A_100
      | E_99 = A_100
      | ~ r2_hidden(E_99,k1_tarski(A_100)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_183])).

tff(c_212,plain,(
    ! [E_99] :
      ( E_99 = '#skF_8'
      | E_99 = '#skF_8'
      | E_99 = '#skF_8'
      | ~ r2_hidden(E_99,k1_relat_1('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_202])).

tff(c_4527,plain,(
    ! [C_7024] :
      ( '#skF_7'('#skF_9',k2_relat_1('#skF_9'),C_7024) = '#skF_8'
      | ~ r2_hidden(C_7024,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_4520,c_212])).

tff(c_4578,plain,(
    ! [C_7177] :
      ( '#skF_7'('#skF_9',k2_relat_1('#skF_9'),C_7177) = '#skF_8'
      | ~ r2_hidden(C_7177,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_4527])).

tff(c_4582,plain,(
    ! [D_61] :
      ( '#skF_7'('#skF_9',k2_relat_1('#skF_9'),k1_funct_1('#skF_9',D_61)) = '#skF_8'
      | ~ r2_hidden(D_61,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_46,c_4578])).

tff(c_5131,plain,(
    ! [D_7789] :
      ( '#skF_7'('#skF_9',k2_relat_1('#skF_9'),k1_funct_1('#skF_9',D_7789)) = '#skF_8'
      | ~ r2_hidden(D_7789,k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_4582])).

tff(c_48,plain,(
    ! [A_22,C_58] :
      ( k1_funct_1(A_22,'#skF_7'(A_22,k2_relat_1(A_22),C_58)) = C_58
      | ~ r2_hidden(C_58,k2_relat_1(A_22))
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_5140,plain,(
    ! [D_7789] :
      ( k1_funct_1('#skF_9',D_7789) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(k1_funct_1('#skF_9',D_7789),k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(D_7789,k1_relat_1('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5131,c_48])).

tff(c_7278,plain,(
    ! [D_11414] :
      ( k1_funct_1('#skF_9',D_11414) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(k1_funct_1('#skF_9',D_11414),k2_relat_1('#skF_9'))
      | ~ r2_hidden(D_11414,k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_5140])).

tff(c_7301,plain,(
    ! [D_61] :
      ( k1_funct_1('#skF_9',D_61) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(D_61,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_46,c_7278])).

tff(c_7348,plain,(
    ! [D_11799] :
      ( k1_funct_1('#skF_9',D_11799) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(D_11799,k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_7301])).

tff(c_7356,plain,(
    ! [C_58] :
      ( k1_funct_1('#skF_9','#skF_7'('#skF_9',k2_relat_1('#skF_9'),C_58)) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(C_58,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_50,c_7348])).

tff(c_8519,plain,(
    ! [C_14095] :
      ( k1_funct_1('#skF_9','#skF_7'('#skF_9',k2_relat_1('#skF_9'),C_14095)) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(C_14095,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_7356])).

tff(c_8552,plain,(
    ! [C_14095] :
      ( k1_funct_1('#skF_9','#skF_8') = C_14095
      | ~ r2_hidden(C_14095,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(C_14095,k2_relat_1('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8519,c_48])).

tff(c_8627,plain,(
    ! [C_14286] :
      ( k1_funct_1('#skF_9','#skF_8') = C_14286
      | ~ r2_hidden(C_14286,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_8552])).

tff(c_8642,plain,(
    ! [B_19] :
      ( '#skF_3'(k2_relat_1('#skF_9'),B_19) = k1_funct_1('#skF_9','#skF_8')
      | k2_relat_1('#skF_9') = k1_xboole_0
      | k2_relat_1('#skF_9') = k1_tarski(B_19) ) ),
    inference(resolution,[status(thm)],[c_36,c_8627])).

tff(c_8770,plain,(
    ! [B_14669] :
      ( '#skF_3'(k2_relat_1('#skF_9'),B_14669) = k1_funct_1('#skF_9','#skF_8')
      | k2_relat_1('#skF_9') = k1_tarski(B_14669) ) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_8642])).

tff(c_34,plain,(
    ! [A_18,B_19] :
      ( '#skF_3'(A_18,B_19) != B_19
      | k1_xboole_0 = A_18
      | k1_tarski(B_19) = A_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_8781,plain,(
    ! [B_14669] :
      ( k1_funct_1('#skF_9','#skF_8') != B_14669
      | k2_relat_1('#skF_9') = k1_xboole_0
      | k2_relat_1('#skF_9') = k1_tarski(B_14669)
      | k2_relat_1('#skF_9') = k1_tarski(B_14669) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8770,c_34])).

tff(c_8965,plain,(
    k1_tarski(k1_funct_1('#skF_9','#skF_8')) = k2_relat_1('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_8781])).

tff(c_64,plain,(
    k1_tarski(k1_funct_1('#skF_9','#skF_8')) != k2_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_8969,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8965,c_64])).

tff(c_8970,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_105])).

tff(c_40,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8976,plain,(
    k1_relat_1('#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8970,c_8970,c_40])).

tff(c_95,plain,(
    ! [A_72] :
      ( k1_relat_1(A_72) != k1_xboole_0
      | k1_xboole_0 = A_72
      | ~ v1_relat_1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_99,plain,
    ( k1_relat_1('#skF_9') != k1_xboole_0
    | k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_70,c_95])).

tff(c_100,plain,(
    k1_relat_1('#skF_9') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_99])).

tff(c_8973,plain,(
    k1_relat_1('#skF_9') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8970,c_100])).

tff(c_8998,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8976,c_8973])).

tff(c_8999,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_99])).

tff(c_9000,plain,(
    k1_relat_1('#skF_9') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_99])).

tff(c_9014,plain,(
    k1_relat_1('#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8999,c_9000])).

tff(c_9015,plain,(
    k1_tarski('#skF_8') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9014,c_66])).

tff(c_9032,plain,(
    ! [A_15052,B_15053] : k1_enumset1(A_15052,A_15052,B_15053) = k2_tarski(A_15052,B_15053) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4,plain,(
    ! [E_7,A_1,B_2] : r2_hidden(E_7,k1_enumset1(A_1,B_2,E_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_9050,plain,(
    ! [B_15054,A_15055] : r2_hidden(B_15054,k2_tarski(A_15055,B_15054)) ),
    inference(superposition,[status(thm),theory(equality)],[c_9032,c_4])).

tff(c_9056,plain,(
    ! [A_15058] : r2_hidden(A_15058,k1_tarski(A_15058)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_9050])).

tff(c_9059,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_9015,c_9056])).

tff(c_38,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_9008,plain,(
    k2_relat_1('#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8999,c_8999,c_38])).

tff(c_9171,plain,(
    ! [A_15082,D_15083] :
      ( r2_hidden(k1_funct_1(A_15082,D_15083),k2_relat_1(A_15082))
      | ~ r2_hidden(D_15083,k1_relat_1(A_15082))
      | ~ v1_funct_1(A_15082)
      | ~ v1_relat_1(A_15082) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_9174,plain,(
    ! [D_15083] :
      ( r2_hidden(k1_funct_1('#skF_9',D_15083),'#skF_9')
      | ~ r2_hidden(D_15083,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9008,c_9171])).

tff(c_9177,plain,(
    ! [D_15084] :
      ( r2_hidden(k1_funct_1('#skF_9',D_15084),'#skF_9')
      | ~ r2_hidden(D_15084,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_9014,c_9174])).

tff(c_9102,plain,(
    ! [E_15072,C_15073,B_15074,A_15075] :
      ( E_15072 = C_15073
      | E_15072 = B_15074
      | E_15072 = A_15075
      | ~ r2_hidden(E_15072,k1_enumset1(A_15075,B_15074,C_15073)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_9126,plain,(
    ! [E_15076,B_15077,A_15078] :
      ( E_15076 = B_15077
      | E_15076 = A_15078
      | E_15076 = A_15078
      | ~ r2_hidden(E_15076,k2_tarski(A_15078,B_15077)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_9102])).

tff(c_9145,plain,(
    ! [E_15079,A_15080] :
      ( E_15079 = A_15080
      | E_15079 = A_15080
      | E_15079 = A_15080
      | ~ r2_hidden(E_15079,k1_tarski(A_15080)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_9126])).

tff(c_9155,plain,(
    ! [E_15079] :
      ( E_15079 = '#skF_8'
      | E_15079 = '#skF_8'
      | E_15079 = '#skF_8'
      | ~ r2_hidden(E_15079,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9015,c_9145])).

tff(c_9182,plain,(
    ! [D_15085] :
      ( k1_funct_1('#skF_9',D_15085) = '#skF_8'
      | ~ r2_hidden(D_15085,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_9177,c_9155])).

tff(c_9196,plain,(
    k1_funct_1('#skF_9','#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_9059,c_9182])).

tff(c_9020,plain,(
    k1_tarski(k1_funct_1('#skF_9','#skF_8')) != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9008,c_64])).

tff(c_9197,plain,(
    k1_tarski('#skF_8') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9196,c_9020])).

tff(c_9200,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9015,c_9197])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:40:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.78/2.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.78/2.36  
% 6.78/2.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.78/2.36  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_1 > #skF_5 > #skF_4
% 6.78/2.36  
% 6.78/2.36  %Foreground sorts:
% 6.78/2.36  
% 6.78/2.36  
% 6.78/2.36  %Background operators:
% 6.78/2.36  
% 6.78/2.36  
% 6.78/2.36  %Foreground operators:
% 6.78/2.36  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 6.78/2.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.78/2.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.78/2.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.78/2.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.78/2.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.78/2.36  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.78/2.36  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.78/2.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.78/2.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.78/2.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.78/2.36  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 6.78/2.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.78/2.36  tff('#skF_9', type, '#skF_9': $i).
% 6.78/2.36  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 6.78/2.36  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.78/2.36  tff('#skF_8', type, '#skF_8': $i).
% 6.78/2.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.78/2.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.78/2.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.78/2.36  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 6.78/2.36  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 6.78/2.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.78/2.36  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.78/2.36  
% 6.78/2.38  tff(f_97, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 6.78/2.38  tff(f_73, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 6.78/2.38  tff(f_62, axiom, (![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 6.78/2.38  tff(f_88, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 6.78/2.38  tff(f_42, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 6.78/2.38  tff(f_44, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 6.78/2.38  tff(f_40, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 6.78/2.38  tff(f_65, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 6.78/2.38  tff(c_70, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.78/2.38  tff(c_101, plain, (![A_73]: (k2_relat_1(A_73)!=k1_xboole_0 | k1_xboole_0=A_73 | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.78/2.38  tff(c_105, plain, (k2_relat_1('#skF_9')!=k1_xboole_0 | k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_70, c_101])).
% 6.78/2.38  tff(c_106, plain, (k2_relat_1('#skF_9')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_105])).
% 6.78/2.38  tff(c_36, plain, (![A_18, B_19]: (r2_hidden('#skF_3'(A_18, B_19), A_18) | k1_xboole_0=A_18 | k1_tarski(B_19)=A_18)), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.78/2.38  tff(c_68, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.78/2.38  tff(c_50, plain, (![A_22, C_58]: (r2_hidden('#skF_7'(A_22, k2_relat_1(A_22), C_58), k1_relat_1(A_22)) | ~r2_hidden(C_58, k2_relat_1(A_22)) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.78/2.38  tff(c_46, plain, (![A_22, D_61]: (r2_hidden(k1_funct_1(A_22, D_61), k2_relat_1(A_22)) | ~r2_hidden(D_61, k1_relat_1(A_22)) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.78/2.38  tff(c_4520, plain, (![A_7023, C_7024]: (r2_hidden('#skF_7'(A_7023, k2_relat_1(A_7023), C_7024), k1_relat_1(A_7023)) | ~r2_hidden(C_7024, k2_relat_1(A_7023)) | ~v1_funct_1(A_7023) | ~v1_relat_1(A_7023))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.78/2.38  tff(c_66, plain, (k1_tarski('#skF_8')=k1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.78/2.38  tff(c_26, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.78/2.38  tff(c_28, plain, (![A_9, B_10]: (k1_enumset1(A_9, A_9, B_10)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.78/2.38  tff(c_159, plain, (![E_92, C_93, B_94, A_95]: (E_92=C_93 | E_92=B_94 | E_92=A_95 | ~r2_hidden(E_92, k1_enumset1(A_95, B_94, C_93)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.78/2.38  tff(c_183, plain, (![E_96, B_97, A_98]: (E_96=B_97 | E_96=A_98 | E_96=A_98 | ~r2_hidden(E_96, k2_tarski(A_98, B_97)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_159])).
% 6.78/2.38  tff(c_202, plain, (![E_99, A_100]: (E_99=A_100 | E_99=A_100 | E_99=A_100 | ~r2_hidden(E_99, k1_tarski(A_100)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_183])).
% 6.78/2.38  tff(c_212, plain, (![E_99]: (E_99='#skF_8' | E_99='#skF_8' | E_99='#skF_8' | ~r2_hidden(E_99, k1_relat_1('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_66, c_202])).
% 6.78/2.38  tff(c_4527, plain, (![C_7024]: ('#skF_7'('#skF_9', k2_relat_1('#skF_9'), C_7024)='#skF_8' | ~r2_hidden(C_7024, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_4520, c_212])).
% 6.78/2.38  tff(c_4578, plain, (![C_7177]: ('#skF_7'('#skF_9', k2_relat_1('#skF_9'), C_7177)='#skF_8' | ~r2_hidden(C_7177, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_4527])).
% 6.78/2.38  tff(c_4582, plain, (![D_61]: ('#skF_7'('#skF_9', k2_relat_1('#skF_9'), k1_funct_1('#skF_9', D_61))='#skF_8' | ~r2_hidden(D_61, k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_46, c_4578])).
% 6.78/2.38  tff(c_5131, plain, (![D_7789]: ('#skF_7'('#skF_9', k2_relat_1('#skF_9'), k1_funct_1('#skF_9', D_7789))='#skF_8' | ~r2_hidden(D_7789, k1_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_4582])).
% 6.78/2.38  tff(c_48, plain, (![A_22, C_58]: (k1_funct_1(A_22, '#skF_7'(A_22, k2_relat_1(A_22), C_58))=C_58 | ~r2_hidden(C_58, k2_relat_1(A_22)) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.78/2.38  tff(c_5140, plain, (![D_7789]: (k1_funct_1('#skF_9', D_7789)=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(k1_funct_1('#skF_9', D_7789), k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(D_7789, k1_relat_1('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_5131, c_48])).
% 6.78/2.38  tff(c_7278, plain, (![D_11414]: (k1_funct_1('#skF_9', D_11414)=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(k1_funct_1('#skF_9', D_11414), k2_relat_1('#skF_9')) | ~r2_hidden(D_11414, k1_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_5140])).
% 6.78/2.38  tff(c_7301, plain, (![D_61]: (k1_funct_1('#skF_9', D_61)=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(D_61, k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_46, c_7278])).
% 6.78/2.38  tff(c_7348, plain, (![D_11799]: (k1_funct_1('#skF_9', D_11799)=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(D_11799, k1_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_7301])).
% 6.78/2.38  tff(c_7356, plain, (![C_58]: (k1_funct_1('#skF_9', '#skF_7'('#skF_9', k2_relat_1('#skF_9'), C_58))=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(C_58, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_50, c_7348])).
% 6.78/2.38  tff(c_8519, plain, (![C_14095]: (k1_funct_1('#skF_9', '#skF_7'('#skF_9', k2_relat_1('#skF_9'), C_14095))=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(C_14095, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_7356])).
% 6.78/2.38  tff(c_8552, plain, (![C_14095]: (k1_funct_1('#skF_9', '#skF_8')=C_14095 | ~r2_hidden(C_14095, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(C_14095, k2_relat_1('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_8519, c_48])).
% 6.78/2.38  tff(c_8627, plain, (![C_14286]: (k1_funct_1('#skF_9', '#skF_8')=C_14286 | ~r2_hidden(C_14286, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_8552])).
% 6.78/2.38  tff(c_8642, plain, (![B_19]: ('#skF_3'(k2_relat_1('#skF_9'), B_19)=k1_funct_1('#skF_9', '#skF_8') | k2_relat_1('#skF_9')=k1_xboole_0 | k2_relat_1('#skF_9')=k1_tarski(B_19))), inference(resolution, [status(thm)], [c_36, c_8627])).
% 6.78/2.38  tff(c_8770, plain, (![B_14669]: ('#skF_3'(k2_relat_1('#skF_9'), B_14669)=k1_funct_1('#skF_9', '#skF_8') | k2_relat_1('#skF_9')=k1_tarski(B_14669))), inference(negUnitSimplification, [status(thm)], [c_106, c_8642])).
% 6.78/2.38  tff(c_34, plain, (![A_18, B_19]: ('#skF_3'(A_18, B_19)!=B_19 | k1_xboole_0=A_18 | k1_tarski(B_19)=A_18)), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.78/2.38  tff(c_8781, plain, (![B_14669]: (k1_funct_1('#skF_9', '#skF_8')!=B_14669 | k2_relat_1('#skF_9')=k1_xboole_0 | k2_relat_1('#skF_9')=k1_tarski(B_14669) | k2_relat_1('#skF_9')=k1_tarski(B_14669))), inference(superposition, [status(thm), theory('equality')], [c_8770, c_34])).
% 6.78/2.38  tff(c_8965, plain, (k1_tarski(k1_funct_1('#skF_9', '#skF_8'))=k2_relat_1('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_106, c_8781])).
% 6.78/2.38  tff(c_64, plain, (k1_tarski(k1_funct_1('#skF_9', '#skF_8'))!=k2_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.78/2.38  tff(c_8969, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8965, c_64])).
% 6.78/2.38  tff(c_8970, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_105])).
% 6.78/2.38  tff(c_40, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.78/2.38  tff(c_8976, plain, (k1_relat_1('#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_8970, c_8970, c_40])).
% 6.78/2.38  tff(c_95, plain, (![A_72]: (k1_relat_1(A_72)!=k1_xboole_0 | k1_xboole_0=A_72 | ~v1_relat_1(A_72))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.78/2.38  tff(c_99, plain, (k1_relat_1('#skF_9')!=k1_xboole_0 | k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_70, c_95])).
% 6.78/2.38  tff(c_100, plain, (k1_relat_1('#skF_9')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_99])).
% 6.78/2.38  tff(c_8973, plain, (k1_relat_1('#skF_9')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_8970, c_100])).
% 6.78/2.38  tff(c_8998, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8976, c_8973])).
% 6.78/2.38  tff(c_8999, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_99])).
% 6.78/2.38  tff(c_9000, plain, (k1_relat_1('#skF_9')=k1_xboole_0), inference(splitRight, [status(thm)], [c_99])).
% 6.78/2.38  tff(c_9014, plain, (k1_relat_1('#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_8999, c_9000])).
% 6.78/2.38  tff(c_9015, plain, (k1_tarski('#skF_8')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_9014, c_66])).
% 6.78/2.38  tff(c_9032, plain, (![A_15052, B_15053]: (k1_enumset1(A_15052, A_15052, B_15053)=k2_tarski(A_15052, B_15053))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.78/2.38  tff(c_4, plain, (![E_7, A_1, B_2]: (r2_hidden(E_7, k1_enumset1(A_1, B_2, E_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.78/2.38  tff(c_9050, plain, (![B_15054, A_15055]: (r2_hidden(B_15054, k2_tarski(A_15055, B_15054)))), inference(superposition, [status(thm), theory('equality')], [c_9032, c_4])).
% 6.78/2.38  tff(c_9056, plain, (![A_15058]: (r2_hidden(A_15058, k1_tarski(A_15058)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_9050])).
% 6.78/2.38  tff(c_9059, plain, (r2_hidden('#skF_8', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_9015, c_9056])).
% 6.78/2.38  tff(c_38, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.78/2.38  tff(c_9008, plain, (k2_relat_1('#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_8999, c_8999, c_38])).
% 6.78/2.38  tff(c_9171, plain, (![A_15082, D_15083]: (r2_hidden(k1_funct_1(A_15082, D_15083), k2_relat_1(A_15082)) | ~r2_hidden(D_15083, k1_relat_1(A_15082)) | ~v1_funct_1(A_15082) | ~v1_relat_1(A_15082))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.78/2.38  tff(c_9174, plain, (![D_15083]: (r2_hidden(k1_funct_1('#skF_9', D_15083), '#skF_9') | ~r2_hidden(D_15083, k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_9008, c_9171])).
% 6.78/2.38  tff(c_9177, plain, (![D_15084]: (r2_hidden(k1_funct_1('#skF_9', D_15084), '#skF_9') | ~r2_hidden(D_15084, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_9014, c_9174])).
% 6.78/2.38  tff(c_9102, plain, (![E_15072, C_15073, B_15074, A_15075]: (E_15072=C_15073 | E_15072=B_15074 | E_15072=A_15075 | ~r2_hidden(E_15072, k1_enumset1(A_15075, B_15074, C_15073)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.78/2.38  tff(c_9126, plain, (![E_15076, B_15077, A_15078]: (E_15076=B_15077 | E_15076=A_15078 | E_15076=A_15078 | ~r2_hidden(E_15076, k2_tarski(A_15078, B_15077)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_9102])).
% 6.78/2.38  tff(c_9145, plain, (![E_15079, A_15080]: (E_15079=A_15080 | E_15079=A_15080 | E_15079=A_15080 | ~r2_hidden(E_15079, k1_tarski(A_15080)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_9126])).
% 6.78/2.38  tff(c_9155, plain, (![E_15079]: (E_15079='#skF_8' | E_15079='#skF_8' | E_15079='#skF_8' | ~r2_hidden(E_15079, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_9015, c_9145])).
% 6.78/2.38  tff(c_9182, plain, (![D_15085]: (k1_funct_1('#skF_9', D_15085)='#skF_8' | ~r2_hidden(D_15085, '#skF_9'))), inference(resolution, [status(thm)], [c_9177, c_9155])).
% 6.78/2.38  tff(c_9196, plain, (k1_funct_1('#skF_9', '#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_9059, c_9182])).
% 6.78/2.38  tff(c_9020, plain, (k1_tarski(k1_funct_1('#skF_9', '#skF_8'))!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_9008, c_64])).
% 6.78/2.38  tff(c_9197, plain, (k1_tarski('#skF_8')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_9196, c_9020])).
% 6.78/2.38  tff(c_9200, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9015, c_9197])).
% 6.78/2.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.78/2.38  
% 6.78/2.38  Inference rules
% 6.78/2.38  ----------------------
% 6.78/2.38  #Ref     : 5
% 6.78/2.38  #Sup     : 1801
% 6.78/2.38  #Fact    : 5
% 6.78/2.38  #Define  : 0
% 6.78/2.38  #Split   : 5
% 6.78/2.38  #Chain   : 0
% 6.78/2.38  #Close   : 0
% 6.78/2.38  
% 6.78/2.38  Ordering : KBO
% 6.78/2.38  
% 6.78/2.38  Simplification rules
% 6.78/2.38  ----------------------
% 6.78/2.38  #Subsume      : 902
% 6.78/2.38  #Demod        : 252
% 6.78/2.38  #Tautology    : 463
% 6.78/2.38  #SimpNegUnit  : 144
% 6.78/2.38  #BackRed      : 16
% 6.78/2.38  
% 6.78/2.38  #Partial instantiations: 7020
% 6.78/2.38  #Strategies tried      : 1
% 6.78/2.38  
% 6.78/2.38  Timing (in seconds)
% 6.78/2.38  ----------------------
% 6.78/2.38  Preprocessing        : 0.31
% 6.78/2.38  Parsing              : 0.15
% 6.78/2.38  CNF conversion       : 0.03
% 6.78/2.38  Main loop            : 1.32
% 6.78/2.38  Inferencing          : 0.49
% 6.78/2.38  Reduction            : 0.38
% 6.78/2.38  Demodulation         : 0.26
% 6.78/2.38  BG Simplification    : 0.05
% 6.78/2.38  Subsumption          : 0.34
% 6.78/2.38  Abstraction          : 0.07
% 6.78/2.38  MUC search           : 0.00
% 6.78/2.38  Cooper               : 0.00
% 6.78/2.38  Total                : 1.66
% 6.78/2.38  Index Insertion      : 0.00
% 6.78/2.38  Index Deletion       : 0.00
% 6.78/2.38  Index Matching       : 0.00
% 6.78/2.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
