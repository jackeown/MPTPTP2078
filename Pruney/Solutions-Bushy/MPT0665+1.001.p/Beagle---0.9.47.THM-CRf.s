%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0665+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:40 EST 2020

% Result     : Theorem 6.79s
% Output     : CNFRefutation 6.79s
% Verified   : 
% Statistics : Number of formulae       :   52 (  97 expanded)
%              Number of leaves         :   27 (  48 expanded)
%              Depth                    :    8
%              Number of atoms          :   84 ( 252 expanded)
%              Number of equality atoms :    7 (  15 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k3_xboole_0 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_1 > #skF_6 > #skF_7 > #skF_3 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_4

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

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r2_hidden(A,k1_relat_1(C))
            & r2_hidden(A,B) )
         => r2_hidden(k1_funct_1(C,A),k2_relat_1(k7_relat_1(C,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_funct_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,B)
       => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_funct_1)).

tff(f_48,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(c_56,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_54,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_40,plain,(
    ! [A_49,B_50] :
      ( v1_funct_1(k7_relat_1(A_49,B_50))
      | ~ v1_funct_1(A_49)
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_52,plain,(
    r2_hidden('#skF_7',k1_relat_1('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_50,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_46,plain,(
    ! [B_55,A_54] :
      ( k3_xboole_0(k1_relat_1(B_55),A_54) = k1_relat_1(k7_relat_1(B_55,A_54))
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_76,plain,(
    ! [D_68,A_69,B_70] :
      ( r2_hidden(D_68,k3_xboole_0(A_69,B_70))
      | ~ r2_hidden(D_68,B_70)
      | ~ r2_hidden(D_68,A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_85,plain,(
    ! [D_68,B_55,A_54] :
      ( r2_hidden(D_68,k1_relat_1(k7_relat_1(B_55,A_54)))
      | ~ r2_hidden(D_68,A_54)
      | ~ r2_hidden(D_68,k1_relat_1(B_55))
      | ~ v1_relat_1(B_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_76])).

tff(c_38,plain,(
    ! [A_47,B_48] :
      ( v1_relat_1(k7_relat_1(A_47,B_48))
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_91,plain,(
    ! [C_79,B_80,A_81] :
      ( k1_funct_1(k7_relat_1(C_79,B_80),A_81) = k1_funct_1(C_79,A_81)
      | ~ r2_hidden(A_81,B_80)
      | ~ v1_funct_1(C_79)
      | ~ v1_relat_1(C_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_20,plain,(
    ! [A_7,D_46] :
      ( r2_hidden(k1_funct_1(A_7,D_46),k2_relat_1(A_7))
      | ~ r2_hidden(D_46,k1_relat_1(A_7))
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_5052,plain,(
    ! [C_346,A_347,B_348] :
      ( r2_hidden(k1_funct_1(C_346,A_347),k2_relat_1(k7_relat_1(C_346,B_348)))
      | ~ r2_hidden(A_347,k1_relat_1(k7_relat_1(C_346,B_348)))
      | ~ v1_funct_1(k7_relat_1(C_346,B_348))
      | ~ v1_relat_1(k7_relat_1(C_346,B_348))
      | ~ r2_hidden(A_347,B_348)
      | ~ v1_funct_1(C_346)
      | ~ v1_relat_1(C_346) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_20])).

tff(c_48,plain,(
    ~ r2_hidden(k1_funct_1('#skF_9','#skF_7'),k2_relat_1(k7_relat_1('#skF_9','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_5059,plain,
    ( ~ r2_hidden('#skF_7',k1_relat_1(k7_relat_1('#skF_9','#skF_8')))
    | ~ v1_funct_1(k7_relat_1('#skF_9','#skF_8'))
    | ~ v1_relat_1(k7_relat_1('#skF_9','#skF_8'))
    | ~ r2_hidden('#skF_7','#skF_8')
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_5052,c_48])).

tff(c_5079,plain,
    ( ~ r2_hidden('#skF_7',k1_relat_1(k7_relat_1('#skF_9','#skF_8')))
    | ~ v1_funct_1(k7_relat_1('#skF_9','#skF_8'))
    | ~ v1_relat_1(k7_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_5059])).

tff(c_5080,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_9','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_5079])).

tff(c_5083,plain,(
    ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_38,c_5080])).

tff(c_5087,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_5083])).

tff(c_5088,plain,
    ( ~ v1_funct_1(k7_relat_1('#skF_9','#skF_8'))
    | ~ r2_hidden('#skF_7',k1_relat_1(k7_relat_1('#skF_9','#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_5079])).

tff(c_5120,plain,(
    ~ r2_hidden('#skF_7',k1_relat_1(k7_relat_1('#skF_9','#skF_8'))) ),
    inference(splitLeft,[status(thm)],[c_5088])).

tff(c_5123,plain,
    ( ~ r2_hidden('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_9'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_85,c_5120])).

tff(c_5127,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_50,c_5123])).

tff(c_5128,plain,(
    ~ v1_funct_1(k7_relat_1('#skF_9','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_5088])).

tff(c_5132,plain,
    ( ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_40,c_5128])).

tff(c_5136,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_5132])).

%------------------------------------------------------------------------------
