%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0673+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:41 EST 2020

% Result     : Theorem 12.00s
% Output     : CNFRefutation 12.00s
% Verified   : 
% Statistics : Number of formulae       :  108 (3158 expanded)
%              Number of leaves         :   22 ( 955 expanded)
%              Depth                    :   28
%              Number of atoms          :  430 (22537 expanded)
%              Number of equality atoms :   65 (3824 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relat_1 > k1_funct_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( v2_funct_1(B)
         => v2_funct_1(k8_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_funct_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v1_relat_1(k8_relat_1(A,B))
        & v1_funct_1(k8_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_funct_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_39,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
      <=> ! [B,C] :
            ( ( r2_hidden(B,k1_relat_1(A))
              & r2_hidden(C,k1_relat_1(A))
              & k1_funct_1(A,B) = k1_funct_1(A,C) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( B = k8_relat_1(A,C)
          <=> ( ! [D] :
                  ( r2_hidden(D,k1_relat_1(B))
                <=> ( r2_hidden(D,k1_relat_1(C))
                    & r2_hidden(k1_funct_1(C,D),A) ) )
              & ! [D] :
                  ( r2_hidden(D,k1_relat_1(B))
                 => k1_funct_1(B,D) = k1_funct_1(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_funct_1)).

tff(c_56,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_54,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( v1_funct_1(k8_relat_1(A_10,B_11))
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( v1_relat_1(k8_relat_1(A_8,B_9))
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_59,plain,(
    ! [A_34] :
      ( '#skF_2'(A_34) != '#skF_1'(A_34)
      | v2_funct_1(A_34)
      | ~ v1_funct_1(A_34)
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_50,plain,(
    ~ v2_funct_1(k8_relat_1('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_63,plain,
    ( '#skF_2'(k8_relat_1('#skF_6','#skF_7')) != '#skF_1'(k8_relat_1('#skF_6','#skF_7'))
    | ~ v1_funct_1(k8_relat_1('#skF_6','#skF_7'))
    | ~ v1_relat_1(k8_relat_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_59,c_50])).

tff(c_66,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_63])).

tff(c_69,plain,(
    ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_12,c_66])).

tff(c_73,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_69])).

tff(c_74,plain,
    ( ~ v1_funct_1(k8_relat_1('#skF_6','#skF_7'))
    | '#skF_2'(k8_relat_1('#skF_6','#skF_7')) != '#skF_1'(k8_relat_1('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_63])).

tff(c_76,plain,(
    '#skF_2'(k8_relat_1('#skF_6','#skF_7')) != '#skF_1'(k8_relat_1('#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_75,plain,(
    v1_relat_1(k8_relat_1('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_63])).

tff(c_28,plain,(
    ! [A_12,B_13,C_23] :
      ( r2_hidden('#skF_3'(A_12,B_13,C_23),k1_relat_1(C_23))
      | r2_hidden('#skF_4'(A_12,B_13,C_23),k1_relat_1(B_13))
      | k1_funct_1(C_23,'#skF_5'(A_12,B_13,C_23)) != k1_funct_1(B_13,'#skF_5'(A_12,B_13,C_23))
      | k8_relat_1(A_12,C_23) = B_13
      | ~ v1_funct_1(C_23)
      | ~ v1_relat_1(C_23)
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_370,plain,(
    ! [A_88,B_89] :
      ( r2_hidden('#skF_3'(A_88,B_89,B_89),k1_relat_1(B_89))
      | r2_hidden('#skF_4'(A_88,B_89,B_89),k1_relat_1(B_89))
      | k8_relat_1(A_88,B_89) = B_89
      | ~ v1_funct_1(B_89)
      | ~ v1_relat_1(B_89)
      | ~ v1_funct_1(B_89)
      | ~ v1_relat_1(B_89) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_28])).

tff(c_48,plain,(
    ! [D_28,C_23,A_12] :
      ( r2_hidden(D_28,k1_relat_1(C_23))
      | ~ r2_hidden(D_28,k1_relat_1(k8_relat_1(A_12,C_23)))
      | ~ v1_funct_1(C_23)
      | ~ v1_relat_1(C_23)
      | ~ v1_funct_1(k8_relat_1(A_12,C_23))
      | ~ v1_relat_1(k8_relat_1(A_12,C_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_385,plain,(
    ! [A_88,A_12,C_23] :
      ( r2_hidden('#skF_4'(A_88,k8_relat_1(A_12,C_23),k8_relat_1(A_12,C_23)),k1_relat_1(C_23))
      | ~ v1_funct_1(C_23)
      | ~ v1_relat_1(C_23)
      | r2_hidden('#skF_3'(A_88,k8_relat_1(A_12,C_23),k8_relat_1(A_12,C_23)),k1_relat_1(k8_relat_1(A_12,C_23)))
      | k8_relat_1(A_88,k8_relat_1(A_12,C_23)) = k8_relat_1(A_12,C_23)
      | ~ v1_funct_1(k8_relat_1(A_12,C_23))
      | ~ v1_relat_1(k8_relat_1(A_12,C_23)) ) ),
    inference(resolution,[status(thm)],[c_370,c_48])).

tff(c_24,plain,(
    ! [A_12,B_13,C_23] :
      ( ~ r2_hidden('#skF_3'(A_12,B_13,C_23),k1_relat_1(B_13))
      | r2_hidden('#skF_4'(A_12,B_13,C_23),k1_relat_1(B_13))
      | k1_funct_1(C_23,'#skF_5'(A_12,B_13,C_23)) != k1_funct_1(B_13,'#skF_5'(A_12,B_13,C_23))
      | k8_relat_1(A_12,C_23) = B_13
      | ~ v1_funct_1(C_23)
      | ~ v1_relat_1(C_23)
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_346,plain,(
    ! [A_80,B_81] :
      ( ~ r2_hidden('#skF_3'(A_80,B_81,B_81),k1_relat_1(B_81))
      | r2_hidden('#skF_4'(A_80,B_81,B_81),k1_relat_1(B_81))
      | k8_relat_1(A_80,B_81) = B_81
      | ~ v1_funct_1(B_81)
      | ~ v1_relat_1(B_81)
      | ~ v1_funct_1(B_81)
      | ~ v1_relat_1(B_81) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_24])).

tff(c_585,plain,(
    ! [A_129,A_130,C_131] :
      ( r2_hidden('#skF_4'(A_129,k8_relat_1(A_130,C_131),k8_relat_1(A_130,C_131)),k1_relat_1(C_131))
      | ~ v1_funct_1(C_131)
      | ~ v1_relat_1(C_131)
      | ~ r2_hidden('#skF_3'(A_129,k8_relat_1(A_130,C_131),k8_relat_1(A_130,C_131)),k1_relat_1(k8_relat_1(A_130,C_131)))
      | k8_relat_1(A_129,k8_relat_1(A_130,C_131)) = k8_relat_1(A_130,C_131)
      | ~ v1_funct_1(k8_relat_1(A_130,C_131))
      | ~ v1_relat_1(k8_relat_1(A_130,C_131)) ) ),
    inference(resolution,[status(thm)],[c_346,c_48])).

tff(c_595,plain,(
    ! [A_88,A_12,C_23] :
      ( r2_hidden('#skF_4'(A_88,k8_relat_1(A_12,C_23),k8_relat_1(A_12,C_23)),k1_relat_1(C_23))
      | ~ v1_funct_1(C_23)
      | ~ v1_relat_1(C_23)
      | k8_relat_1(A_88,k8_relat_1(A_12,C_23)) = k8_relat_1(A_12,C_23)
      | ~ v1_funct_1(k8_relat_1(A_12,C_23))
      | ~ v1_relat_1(k8_relat_1(A_12,C_23)) ) ),
    inference(resolution,[status(thm)],[c_385,c_585])).

tff(c_46,plain,(
    ! [C_23,D_28,A_12] :
      ( r2_hidden(k1_funct_1(C_23,D_28),A_12)
      | ~ r2_hidden(D_28,k1_relat_1(k8_relat_1(A_12,C_23)))
      | ~ v1_funct_1(C_23)
      | ~ v1_relat_1(C_23)
      | ~ v1_funct_1(k8_relat_1(A_12,C_23))
      | ~ v1_relat_1(k8_relat_1(A_12,C_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_384,plain,(
    ! [C_23,A_88,A_12] :
      ( r2_hidden(k1_funct_1(C_23,'#skF_4'(A_88,k8_relat_1(A_12,C_23),k8_relat_1(A_12,C_23))),A_12)
      | ~ v1_funct_1(C_23)
      | ~ v1_relat_1(C_23)
      | r2_hidden('#skF_3'(A_88,k8_relat_1(A_12,C_23),k8_relat_1(A_12,C_23)),k1_relat_1(k8_relat_1(A_12,C_23)))
      | k8_relat_1(A_88,k8_relat_1(A_12,C_23)) = k8_relat_1(A_12,C_23)
      | ~ v1_funct_1(k8_relat_1(A_12,C_23))
      | ~ v1_relat_1(k8_relat_1(A_12,C_23)) ) ),
    inference(resolution,[status(thm)],[c_370,c_46])).

tff(c_699,plain,(
    ! [C_153,A_154,A_155] :
      ( r2_hidden(k1_funct_1(C_153,'#skF_4'(A_154,k8_relat_1(A_155,C_153),k8_relat_1(A_155,C_153))),A_155)
      | ~ v1_funct_1(C_153)
      | ~ v1_relat_1(C_153)
      | ~ r2_hidden('#skF_3'(A_154,k8_relat_1(A_155,C_153),k8_relat_1(A_155,C_153)),k1_relat_1(k8_relat_1(A_155,C_153)))
      | k8_relat_1(A_154,k8_relat_1(A_155,C_153)) = k8_relat_1(A_155,C_153)
      | ~ v1_funct_1(k8_relat_1(A_155,C_153))
      | ~ v1_relat_1(k8_relat_1(A_155,C_153)) ) ),
    inference(resolution,[status(thm)],[c_346,c_46])).

tff(c_709,plain,(
    ! [C_23,A_88,A_12] :
      ( r2_hidden(k1_funct_1(C_23,'#skF_4'(A_88,k8_relat_1(A_12,C_23),k8_relat_1(A_12,C_23))),A_12)
      | ~ v1_funct_1(C_23)
      | ~ v1_relat_1(C_23)
      | k8_relat_1(A_88,k8_relat_1(A_12,C_23)) = k8_relat_1(A_12,C_23)
      | ~ v1_funct_1(k8_relat_1(A_12,C_23))
      | ~ v1_relat_1(k8_relat_1(A_12,C_23)) ) ),
    inference(resolution,[status(thm)],[c_384,c_699])).

tff(c_44,plain,(
    ! [D_28,A_12,C_23] :
      ( r2_hidden(D_28,k1_relat_1(k8_relat_1(A_12,C_23)))
      | ~ r2_hidden(k1_funct_1(C_23,D_28),A_12)
      | ~ r2_hidden(D_28,k1_relat_1(C_23))
      | ~ v1_funct_1(C_23)
      | ~ v1_relat_1(C_23)
      | ~ v1_funct_1(k8_relat_1(A_12,C_23))
      | ~ v1_relat_1(k8_relat_1(A_12,C_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_711,plain,(
    ! [C_156,A_157,A_158] :
      ( r2_hidden(k1_funct_1(C_156,'#skF_4'(A_157,k8_relat_1(A_158,C_156),k8_relat_1(A_158,C_156))),A_158)
      | ~ v1_funct_1(C_156)
      | ~ v1_relat_1(C_156)
      | k8_relat_1(A_157,k8_relat_1(A_158,C_156)) = k8_relat_1(A_158,C_156)
      | ~ v1_funct_1(k8_relat_1(A_158,C_156))
      | ~ v1_relat_1(k8_relat_1(A_158,C_156)) ) ),
    inference(resolution,[status(thm)],[c_384,c_699])).

tff(c_192,plain,(
    ! [D_58,A_59,C_60] :
      ( r2_hidden(D_58,k1_relat_1(k8_relat_1(A_59,C_60)))
      | ~ r2_hidden(k1_funct_1(C_60,D_58),A_59)
      | ~ r2_hidden(D_58,k1_relat_1(C_60))
      | ~ v1_funct_1(C_60)
      | ~ v1_relat_1(C_60)
      | ~ v1_funct_1(k8_relat_1(A_59,C_60))
      | ~ v1_relat_1(k8_relat_1(A_59,C_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_42,plain,(
    ! [A_12,C_23,D_29] :
      ( k1_funct_1(k8_relat_1(A_12,C_23),D_29) = k1_funct_1(C_23,D_29)
      | ~ r2_hidden(D_29,k1_relat_1(k8_relat_1(A_12,C_23)))
      | ~ v1_funct_1(C_23)
      | ~ v1_relat_1(C_23)
      | ~ v1_funct_1(k8_relat_1(A_12,C_23))
      | ~ v1_relat_1(k8_relat_1(A_12,C_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_202,plain,(
    ! [A_59,C_60,D_58] :
      ( k1_funct_1(k8_relat_1(A_59,C_60),D_58) = k1_funct_1(C_60,D_58)
      | ~ r2_hidden(k1_funct_1(C_60,D_58),A_59)
      | ~ r2_hidden(D_58,k1_relat_1(C_60))
      | ~ v1_funct_1(C_60)
      | ~ v1_relat_1(C_60)
      | ~ v1_funct_1(k8_relat_1(A_59,C_60))
      | ~ v1_relat_1(k8_relat_1(A_59,C_60)) ) ),
    inference(resolution,[status(thm)],[c_192,c_42])).

tff(c_1672,plain,(
    ! [A_268,C_269,A_270] :
      ( k1_funct_1(k8_relat_1(A_268,C_269),'#skF_4'(A_270,k8_relat_1(A_268,C_269),k8_relat_1(A_268,C_269))) = k1_funct_1(C_269,'#skF_4'(A_270,k8_relat_1(A_268,C_269),k8_relat_1(A_268,C_269)))
      | ~ r2_hidden('#skF_4'(A_270,k8_relat_1(A_268,C_269),k8_relat_1(A_268,C_269)),k1_relat_1(C_269))
      | ~ v1_funct_1(C_269)
      | ~ v1_relat_1(C_269)
      | k8_relat_1(A_270,k8_relat_1(A_268,C_269)) = k8_relat_1(A_268,C_269)
      | ~ v1_funct_1(k8_relat_1(A_268,C_269))
      | ~ v1_relat_1(k8_relat_1(A_268,C_269)) ) ),
    inference(resolution,[status(thm)],[c_711,c_202])).

tff(c_1680,plain,(
    ! [A_12,C_23,A_88] :
      ( k1_funct_1(k8_relat_1(A_12,C_23),'#skF_4'(A_88,k8_relat_1(A_12,C_23),k8_relat_1(A_12,C_23))) = k1_funct_1(C_23,'#skF_4'(A_88,k8_relat_1(A_12,C_23),k8_relat_1(A_12,C_23)))
      | ~ v1_funct_1(C_23)
      | ~ v1_relat_1(C_23)
      | k8_relat_1(A_88,k8_relat_1(A_12,C_23)) = k8_relat_1(A_12,C_23)
      | ~ v1_funct_1(k8_relat_1(A_12,C_23))
      | ~ v1_relat_1(k8_relat_1(A_12,C_23)) ) ),
    inference(resolution,[status(thm)],[c_595,c_1672])).

tff(c_364,plain,(
    ! [A_12,B_13] :
      ( r2_hidden('#skF_3'(A_12,B_13,B_13),k1_relat_1(B_13))
      | r2_hidden('#skF_4'(A_12,B_13,B_13),k1_relat_1(B_13))
      | k8_relat_1(A_12,B_13) = B_13
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13)
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_28])).

tff(c_1682,plain,(
    ! [A_271,C_272,A_273] :
      ( k1_funct_1(k8_relat_1(A_271,C_272),'#skF_4'(A_273,k8_relat_1(A_271,C_272),k8_relat_1(A_271,C_272))) = k1_funct_1(C_272,'#skF_4'(A_273,k8_relat_1(A_271,C_272),k8_relat_1(A_271,C_272)))
      | ~ v1_funct_1(C_272)
      | ~ v1_relat_1(C_272)
      | k8_relat_1(A_273,k8_relat_1(A_271,C_272)) = k8_relat_1(A_271,C_272)
      | ~ v1_funct_1(k8_relat_1(A_271,C_272))
      | ~ v1_relat_1(k8_relat_1(A_271,C_272)) ) ),
    inference(resolution,[status(thm)],[c_595,c_1672])).

tff(c_22,plain,(
    ! [A_12,B_13,C_23] :
      ( r2_hidden('#skF_3'(A_12,B_13,C_23),k1_relat_1(C_23))
      | ~ r2_hidden(k1_funct_1(C_23,'#skF_4'(A_12,B_13,C_23)),A_12)
      | ~ r2_hidden('#skF_4'(A_12,B_13,C_23),k1_relat_1(C_23))
      | k1_funct_1(C_23,'#skF_5'(A_12,B_13,C_23)) != k1_funct_1(B_13,'#skF_5'(A_12,B_13,C_23))
      | k8_relat_1(A_12,C_23) = B_13
      | ~ v1_funct_1(C_23)
      | ~ v1_relat_1(C_23)
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2303,plain,(
    ! [A_309,A_310,C_311] :
      ( r2_hidden('#skF_3'(A_309,k8_relat_1(A_310,C_311),k8_relat_1(A_310,C_311)),k1_relat_1(k8_relat_1(A_310,C_311)))
      | ~ r2_hidden(k1_funct_1(C_311,'#skF_4'(A_309,k8_relat_1(A_310,C_311),k8_relat_1(A_310,C_311))),A_309)
      | ~ r2_hidden('#skF_4'(A_309,k8_relat_1(A_310,C_311),k8_relat_1(A_310,C_311)),k1_relat_1(k8_relat_1(A_310,C_311)))
      | ~ v1_funct_1(C_311)
      | ~ v1_relat_1(C_311)
      | k8_relat_1(A_309,k8_relat_1(A_310,C_311)) = k8_relat_1(A_310,C_311)
      | ~ v1_funct_1(k8_relat_1(A_310,C_311))
      | ~ v1_relat_1(k8_relat_1(A_310,C_311)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1682,c_22])).

tff(c_2319,plain,(
    ! [A_312,C_313] :
      ( r2_hidden('#skF_3'(A_312,k8_relat_1(A_312,C_313),k8_relat_1(A_312,C_313)),k1_relat_1(k8_relat_1(A_312,C_313)))
      | ~ r2_hidden('#skF_4'(A_312,k8_relat_1(A_312,C_313),k8_relat_1(A_312,C_313)),k1_relat_1(k8_relat_1(A_312,C_313)))
      | ~ v1_funct_1(C_313)
      | ~ v1_relat_1(C_313)
      | k8_relat_1(A_312,k8_relat_1(A_312,C_313)) = k8_relat_1(A_312,C_313)
      | ~ v1_funct_1(k8_relat_1(A_312,C_313))
      | ~ v1_relat_1(k8_relat_1(A_312,C_313)) ) ),
    inference(resolution,[status(thm)],[c_709,c_2303])).

tff(c_2369,plain,(
    ! [C_314,A_315] :
      ( ~ v1_funct_1(C_314)
      | ~ v1_relat_1(C_314)
      | r2_hidden('#skF_3'(A_315,k8_relat_1(A_315,C_314),k8_relat_1(A_315,C_314)),k1_relat_1(k8_relat_1(A_315,C_314)))
      | k8_relat_1(A_315,k8_relat_1(A_315,C_314)) = k8_relat_1(A_315,C_314)
      | ~ v1_funct_1(k8_relat_1(A_315,C_314))
      | ~ v1_relat_1(k8_relat_1(A_315,C_314)) ) ),
    inference(resolution,[status(thm)],[c_364,c_2319])).

tff(c_18,plain,(
    ! [A_12,B_13,C_23] :
      ( ~ r2_hidden('#skF_3'(A_12,B_13,C_23),k1_relat_1(B_13))
      | ~ r2_hidden(k1_funct_1(C_23,'#skF_4'(A_12,B_13,C_23)),A_12)
      | ~ r2_hidden('#skF_4'(A_12,B_13,C_23),k1_relat_1(C_23))
      | k1_funct_1(C_23,'#skF_5'(A_12,B_13,C_23)) != k1_funct_1(B_13,'#skF_5'(A_12,B_13,C_23))
      | k8_relat_1(A_12,C_23) = B_13
      | ~ v1_funct_1(C_23)
      | ~ v1_relat_1(C_23)
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2561,plain,(
    ! [A_326,C_327] :
      ( ~ r2_hidden(k1_funct_1(k8_relat_1(A_326,C_327),'#skF_4'(A_326,k8_relat_1(A_326,C_327),k8_relat_1(A_326,C_327))),A_326)
      | ~ r2_hidden('#skF_4'(A_326,k8_relat_1(A_326,C_327),k8_relat_1(A_326,C_327)),k1_relat_1(k8_relat_1(A_326,C_327)))
      | ~ v1_funct_1(C_327)
      | ~ v1_relat_1(C_327)
      | k8_relat_1(A_326,k8_relat_1(A_326,C_327)) = k8_relat_1(A_326,C_327)
      | ~ v1_funct_1(k8_relat_1(A_326,C_327))
      | ~ v1_relat_1(k8_relat_1(A_326,C_327)) ) ),
    inference(resolution,[status(thm)],[c_2369,c_18])).

tff(c_4163,plain,(
    ! [C_463,A_464] :
      ( ~ r2_hidden(k1_funct_1(C_463,'#skF_4'(A_464,k8_relat_1(A_464,C_463),k8_relat_1(A_464,C_463))),A_464)
      | ~ r2_hidden('#skF_4'(A_464,k8_relat_1(A_464,C_463),k8_relat_1(A_464,C_463)),k1_relat_1(k8_relat_1(A_464,C_463)))
      | ~ v1_funct_1(C_463)
      | ~ v1_relat_1(C_463)
      | k8_relat_1(A_464,k8_relat_1(A_464,C_463)) = k8_relat_1(A_464,C_463)
      | ~ v1_funct_1(k8_relat_1(A_464,C_463))
      | ~ v1_relat_1(k8_relat_1(A_464,C_463))
      | ~ v1_funct_1(C_463)
      | ~ v1_relat_1(C_463)
      | k8_relat_1(A_464,k8_relat_1(A_464,C_463)) = k8_relat_1(A_464,C_463)
      | ~ v1_funct_1(k8_relat_1(A_464,C_463))
      | ~ v1_relat_1(k8_relat_1(A_464,C_463)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1680,c_2561])).

tff(c_4217,plain,(
    ! [A_465,C_466] :
      ( k8_relat_1(A_465,k8_relat_1(A_465,C_466)) = k8_relat_1(A_465,C_466)
      | ~ r2_hidden(k1_funct_1(C_466,'#skF_4'(A_465,k8_relat_1(A_465,C_466),k8_relat_1(A_465,C_466))),A_465)
      | ~ r2_hidden('#skF_4'(A_465,k8_relat_1(A_465,C_466),k8_relat_1(A_465,C_466)),k1_relat_1(C_466))
      | ~ v1_funct_1(C_466)
      | ~ v1_relat_1(C_466)
      | ~ v1_funct_1(k8_relat_1(A_465,C_466))
      | ~ v1_relat_1(k8_relat_1(A_465,C_466)) ) ),
    inference(resolution,[status(thm)],[c_44,c_4163])).

tff(c_4307,plain,(
    ! [A_471,C_472] :
      ( ~ r2_hidden('#skF_4'(A_471,k8_relat_1(A_471,C_472),k8_relat_1(A_471,C_472)),k1_relat_1(C_472))
      | ~ v1_funct_1(C_472)
      | ~ v1_relat_1(C_472)
      | k8_relat_1(A_471,k8_relat_1(A_471,C_472)) = k8_relat_1(A_471,C_472)
      | ~ v1_funct_1(k8_relat_1(A_471,C_472))
      | ~ v1_relat_1(k8_relat_1(A_471,C_472)) ) ),
    inference(resolution,[status(thm)],[c_709,c_4217])).

tff(c_4331,plain,(
    ! [C_473,A_474] :
      ( ~ v1_funct_1(C_473)
      | ~ v1_relat_1(C_473)
      | k8_relat_1(A_474,k8_relat_1(A_474,C_473)) = k8_relat_1(A_474,C_473)
      | ~ v1_funct_1(k8_relat_1(A_474,C_473))
      | ~ v1_relat_1(k8_relat_1(A_474,C_473)) ) ),
    inference(resolution,[status(thm)],[c_595,c_4307])).

tff(c_4333,plain,
    ( ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7')
    | k8_relat_1('#skF_6',k8_relat_1('#skF_6','#skF_7')) = k8_relat_1('#skF_6','#skF_7')
    | ~ v1_funct_1(k8_relat_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_75,c_4331])).

tff(c_4338,plain,
    ( k8_relat_1('#skF_6',k8_relat_1('#skF_6','#skF_7')) = k8_relat_1('#skF_6','#skF_7')
    | ~ v1_funct_1(k8_relat_1('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_4333])).

tff(c_4340,plain,(
    ~ v1_funct_1(k8_relat_1('#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_4338])).

tff(c_4343,plain,
    ( ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_14,c_4340])).

tff(c_4347,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_4343])).

tff(c_4348,plain,(
    k8_relat_1('#skF_6',k8_relat_1('#skF_6','#skF_7')) = k8_relat_1('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_4338])).

tff(c_4349,plain,(
    v1_funct_1(k8_relat_1('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_4338])).

tff(c_10,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),k1_relat_1(A_1))
      | v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_95,plain,(
    ! [D_41,C_42,A_43] :
      ( r2_hidden(D_41,k1_relat_1(C_42))
      | ~ r2_hidden(D_41,k1_relat_1(k8_relat_1(A_43,C_42)))
      | ~ v1_funct_1(C_42)
      | ~ v1_relat_1(C_42)
      | ~ v1_funct_1(k8_relat_1(A_43,C_42))
      | ~ v1_relat_1(k8_relat_1(A_43,C_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_117,plain,(
    ! [A_47,C_48] :
      ( r2_hidden('#skF_1'(k8_relat_1(A_47,C_48)),k1_relat_1(C_48))
      | ~ v1_funct_1(C_48)
      | ~ v1_relat_1(C_48)
      | v2_funct_1(k8_relat_1(A_47,C_48))
      | ~ v1_funct_1(k8_relat_1(A_47,C_48))
      | ~ v1_relat_1(k8_relat_1(A_47,C_48)) ) ),
    inference(resolution,[status(thm)],[c_10,c_95])).

tff(c_127,plain,(
    ! [A_47,A_12,C_23] :
      ( r2_hidden('#skF_1'(k8_relat_1(A_47,k8_relat_1(A_12,C_23))),k1_relat_1(C_23))
      | ~ v1_funct_1(C_23)
      | ~ v1_relat_1(C_23)
      | ~ v1_funct_1(k8_relat_1(A_12,C_23))
      | ~ v1_relat_1(k8_relat_1(A_12,C_23))
      | v2_funct_1(k8_relat_1(A_47,k8_relat_1(A_12,C_23)))
      | ~ v1_funct_1(k8_relat_1(A_47,k8_relat_1(A_12,C_23)))
      | ~ v1_relat_1(k8_relat_1(A_47,k8_relat_1(A_12,C_23))) ) ),
    inference(resolution,[status(thm)],[c_117,c_48])).

tff(c_4855,plain,
    ( r2_hidden('#skF_1'(k8_relat_1('#skF_6','#skF_7')),k1_relat_1('#skF_7'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7')
    | ~ v1_funct_1(k8_relat_1('#skF_6','#skF_7'))
    | ~ v1_relat_1(k8_relat_1('#skF_6','#skF_7'))
    | v2_funct_1(k8_relat_1('#skF_6',k8_relat_1('#skF_6','#skF_7')))
    | ~ v1_funct_1(k8_relat_1('#skF_6',k8_relat_1('#skF_6','#skF_7')))
    | ~ v1_relat_1(k8_relat_1('#skF_6',k8_relat_1('#skF_6','#skF_7'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_4348,c_127])).

tff(c_5242,plain,
    ( r2_hidden('#skF_1'(k8_relat_1('#skF_6','#skF_7')),k1_relat_1('#skF_7'))
    | v2_funct_1(k8_relat_1('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_4348,c_4349,c_4348,c_4348,c_75,c_4349,c_56,c_54,c_4855])).

tff(c_5243,plain,(
    r2_hidden('#skF_1'(k8_relat_1('#skF_6','#skF_7')),k1_relat_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_5242])).

tff(c_52,plain,(
    v2_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_8,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_2'(A_1),k1_relat_1(A_1))
      | v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_144,plain,(
    ! [A_52,C_53] :
      ( r2_hidden('#skF_2'(k8_relat_1(A_52,C_53)),k1_relat_1(C_53))
      | ~ v1_funct_1(C_53)
      | ~ v1_relat_1(C_53)
      | v2_funct_1(k8_relat_1(A_52,C_53))
      | ~ v1_funct_1(k8_relat_1(A_52,C_53))
      | ~ v1_relat_1(k8_relat_1(A_52,C_53)) ) ),
    inference(resolution,[status(thm)],[c_8,c_95])).

tff(c_159,plain,(
    ! [A_52,A_12,C_23] :
      ( r2_hidden('#skF_2'(k8_relat_1(A_52,k8_relat_1(A_12,C_23))),k1_relat_1(C_23))
      | ~ v1_funct_1(C_23)
      | ~ v1_relat_1(C_23)
      | ~ v1_funct_1(k8_relat_1(A_12,C_23))
      | ~ v1_relat_1(k8_relat_1(A_12,C_23))
      | v2_funct_1(k8_relat_1(A_52,k8_relat_1(A_12,C_23)))
      | ~ v1_funct_1(k8_relat_1(A_52,k8_relat_1(A_12,C_23)))
      | ~ v1_relat_1(k8_relat_1(A_52,k8_relat_1(A_12,C_23))) ) ),
    inference(resolution,[status(thm)],[c_144,c_48])).

tff(c_4849,plain,
    ( r2_hidden('#skF_2'(k8_relat_1('#skF_6','#skF_7')),k1_relat_1('#skF_7'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7')
    | ~ v1_funct_1(k8_relat_1('#skF_6','#skF_7'))
    | ~ v1_relat_1(k8_relat_1('#skF_6','#skF_7'))
    | v2_funct_1(k8_relat_1('#skF_6',k8_relat_1('#skF_6','#skF_7')))
    | ~ v1_funct_1(k8_relat_1('#skF_6',k8_relat_1('#skF_6','#skF_7')))
    | ~ v1_relat_1(k8_relat_1('#skF_6',k8_relat_1('#skF_6','#skF_7'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_4348,c_159])).

tff(c_5237,plain,
    ( r2_hidden('#skF_2'(k8_relat_1('#skF_6','#skF_7')),k1_relat_1('#skF_7'))
    | v2_funct_1(k8_relat_1('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_4348,c_4349,c_4348,c_4348,c_75,c_4349,c_56,c_54,c_4849])).

tff(c_5238,plain,(
    r2_hidden('#skF_2'(k8_relat_1('#skF_6','#skF_7')),k1_relat_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_5237])).

tff(c_104,plain,(
    ! [A_43,C_42] :
      ( r2_hidden('#skF_1'(k8_relat_1(A_43,C_42)),k1_relat_1(C_42))
      | ~ v1_funct_1(C_42)
      | ~ v1_relat_1(C_42)
      | v2_funct_1(k8_relat_1(A_43,C_42))
      | ~ v1_funct_1(k8_relat_1(A_43,C_42))
      | ~ v1_relat_1(k8_relat_1(A_43,C_42)) ) ),
    inference(resolution,[status(thm)],[c_10,c_95])).

tff(c_128,plain,(
    ! [A_49,C_50,D_51] :
      ( k1_funct_1(k8_relat_1(A_49,C_50),D_51) = k1_funct_1(C_50,D_51)
      | ~ r2_hidden(D_51,k1_relat_1(k8_relat_1(A_49,C_50)))
      | ~ v1_funct_1(C_50)
      | ~ v1_relat_1(C_50)
      | ~ v1_funct_1(k8_relat_1(A_49,C_50))
      | ~ v1_relat_1(k8_relat_1(A_49,C_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_141,plain,(
    ! [A_49,C_50,A_43] :
      ( k1_funct_1(k8_relat_1(A_49,C_50),'#skF_1'(k8_relat_1(A_43,k8_relat_1(A_49,C_50)))) = k1_funct_1(C_50,'#skF_1'(k8_relat_1(A_43,k8_relat_1(A_49,C_50))))
      | ~ v1_funct_1(C_50)
      | ~ v1_relat_1(C_50)
      | ~ v1_funct_1(k8_relat_1(A_49,C_50))
      | ~ v1_relat_1(k8_relat_1(A_49,C_50))
      | v2_funct_1(k8_relat_1(A_43,k8_relat_1(A_49,C_50)))
      | ~ v1_funct_1(k8_relat_1(A_43,k8_relat_1(A_49,C_50)))
      | ~ v1_relat_1(k8_relat_1(A_43,k8_relat_1(A_49,C_50))) ) ),
    inference(resolution,[status(thm)],[c_104,c_128])).

tff(c_4807,plain,
    ( k1_funct_1(k8_relat_1('#skF_6','#skF_7'),'#skF_1'(k8_relat_1('#skF_6','#skF_7'))) = k1_funct_1('#skF_7','#skF_1'(k8_relat_1('#skF_6',k8_relat_1('#skF_6','#skF_7'))))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7')
    | ~ v1_funct_1(k8_relat_1('#skF_6','#skF_7'))
    | ~ v1_relat_1(k8_relat_1('#skF_6','#skF_7'))
    | v2_funct_1(k8_relat_1('#skF_6',k8_relat_1('#skF_6','#skF_7')))
    | ~ v1_funct_1(k8_relat_1('#skF_6',k8_relat_1('#skF_6','#skF_7')))
    | ~ v1_relat_1(k8_relat_1('#skF_6',k8_relat_1('#skF_6','#skF_7'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_4348,c_141])).

tff(c_5204,plain,
    ( k1_funct_1(k8_relat_1('#skF_6','#skF_7'),'#skF_1'(k8_relat_1('#skF_6','#skF_7'))) = k1_funct_1('#skF_7','#skF_1'(k8_relat_1('#skF_6','#skF_7')))
    | v2_funct_1(k8_relat_1('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_4348,c_4349,c_4348,c_4348,c_75,c_4349,c_56,c_54,c_4348,c_4807])).

tff(c_5205,plain,(
    k1_funct_1(k8_relat_1('#skF_6','#skF_7'),'#skF_1'(k8_relat_1('#skF_6','#skF_7'))) = k1_funct_1('#skF_7','#skF_1'(k8_relat_1('#skF_6','#skF_7'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_5204])).

tff(c_238,plain,(
    ! [A_67,C_68] :
      ( k1_funct_1(k8_relat_1(A_67,C_68),'#skF_2'(k8_relat_1(A_67,C_68))) = k1_funct_1(C_68,'#skF_2'(k8_relat_1(A_67,C_68)))
      | ~ v1_funct_1(C_68)
      | ~ v1_relat_1(C_68)
      | v2_funct_1(k8_relat_1(A_67,C_68))
      | ~ v1_funct_1(k8_relat_1(A_67,C_68))
      | ~ v1_relat_1(k8_relat_1(A_67,C_68)) ) ),
    inference(resolution,[status(thm)],[c_8,c_128])).

tff(c_6,plain,(
    ! [A_1] :
      ( k1_funct_1(A_1,'#skF_2'(A_1)) = k1_funct_1(A_1,'#skF_1'(A_1))
      | v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_251,plain,(
    ! [A_67,C_68] :
      ( k1_funct_1(k8_relat_1(A_67,C_68),'#skF_1'(k8_relat_1(A_67,C_68))) = k1_funct_1(C_68,'#skF_2'(k8_relat_1(A_67,C_68)))
      | v2_funct_1(k8_relat_1(A_67,C_68))
      | ~ v1_funct_1(k8_relat_1(A_67,C_68))
      | ~ v1_relat_1(k8_relat_1(A_67,C_68))
      | ~ v1_funct_1(C_68)
      | ~ v1_relat_1(C_68)
      | v2_funct_1(k8_relat_1(A_67,C_68))
      | ~ v1_funct_1(k8_relat_1(A_67,C_68))
      | ~ v1_relat_1(k8_relat_1(A_67,C_68)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_6])).

tff(c_5615,plain,
    ( k1_funct_1('#skF_7','#skF_2'(k8_relat_1('#skF_6','#skF_7'))) = k1_funct_1('#skF_7','#skF_1'(k8_relat_1('#skF_6','#skF_7')))
    | v2_funct_1(k8_relat_1('#skF_6','#skF_7'))
    | ~ v1_funct_1(k8_relat_1('#skF_6','#skF_7'))
    | ~ v1_relat_1(k8_relat_1('#skF_6','#skF_7'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7')
    | v2_funct_1(k8_relat_1('#skF_6','#skF_7'))
    | ~ v1_funct_1(k8_relat_1('#skF_6','#skF_7'))
    | ~ v1_relat_1(k8_relat_1('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5205,c_251])).

tff(c_5640,plain,
    ( k1_funct_1('#skF_7','#skF_2'(k8_relat_1('#skF_6','#skF_7'))) = k1_funct_1('#skF_7','#skF_1'(k8_relat_1('#skF_6','#skF_7')))
    | v2_funct_1(k8_relat_1('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_4349,c_56,c_54,c_75,c_4349,c_5615])).

tff(c_5641,plain,(
    k1_funct_1('#skF_7','#skF_2'(k8_relat_1('#skF_6','#skF_7'))) = k1_funct_1('#skF_7','#skF_1'(k8_relat_1('#skF_6','#skF_7'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_5640])).

tff(c_2,plain,(
    ! [C_7,B_6,A_1] :
      ( C_7 = B_6
      | k1_funct_1(A_1,C_7) != k1_funct_1(A_1,B_6)
      | ~ r2_hidden(C_7,k1_relat_1(A_1))
      | ~ r2_hidden(B_6,k1_relat_1(A_1))
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_5703,plain,(
    ! [B_6] :
      ( B_6 = '#skF_2'(k8_relat_1('#skF_6','#skF_7'))
      | k1_funct_1('#skF_7',B_6) != k1_funct_1('#skF_7','#skF_1'(k8_relat_1('#skF_6','#skF_7')))
      | ~ r2_hidden('#skF_2'(k8_relat_1('#skF_6','#skF_7')),k1_relat_1('#skF_7'))
      | ~ r2_hidden(B_6,k1_relat_1('#skF_7'))
      | ~ v2_funct_1('#skF_7')
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5641,c_2])).

tff(c_5721,plain,(
    ! [B_6] :
      ( B_6 = '#skF_2'(k8_relat_1('#skF_6','#skF_7'))
      | k1_funct_1('#skF_7',B_6) != k1_funct_1('#skF_7','#skF_1'(k8_relat_1('#skF_6','#skF_7')))
      | ~ r2_hidden(B_6,k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_5238,c_5703])).

tff(c_6547,plain,
    ( '#skF_2'(k8_relat_1('#skF_6','#skF_7')) = '#skF_1'(k8_relat_1('#skF_6','#skF_7'))
    | ~ r2_hidden('#skF_1'(k8_relat_1('#skF_6','#skF_7')),k1_relat_1('#skF_7')) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_5721])).

tff(c_6549,plain,(
    '#skF_2'(k8_relat_1('#skF_6','#skF_7')) = '#skF_1'(k8_relat_1('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5243,c_6547])).

tff(c_6551,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_6549])).

tff(c_6552,plain,(
    ~ v1_funct_1(k8_relat_1('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_6556,plain,
    ( ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_14,c_6552])).

tff(c_6560,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_6556])).

%------------------------------------------------------------------------------
