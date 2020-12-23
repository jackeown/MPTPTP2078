%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:46 EST 2020

% Result     : Theorem 5.93s
% Output     : CNFRefutation 6.02s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 510 expanded)
%              Number of leaves         :   26 ( 193 expanded)
%              Depth                    :   29
%              Number of atoms          :  264 (1615 expanded)
%              Number of equality atoms :   54 ( 470 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_100,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( ( v2_funct_1(B)
            & r2_hidden(A,k2_relat_1(B)) )
         => ( A = k1_funct_1(B,k1_funct_1(k2_funct_1(B),A))
            & A = k1_funct_1(k5_relat_1(k2_funct_1(B),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_funct_1)).

tff(f_46,axiom,(
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

tff(f_62,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_54,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( v2_funct_1(B)
          & r2_hidden(A,k1_relat_1(B)) )
       => ( A = k1_funct_1(k2_funct_1(B),k1_funct_1(B,A))
          & A = k1_funct_1(k5_relat_1(B,k2_funct_1(B)),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

tff(c_44,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_42,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_38,plain,(
    r2_hidden('#skF_5',k2_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_8,plain,(
    ! [A_2,C_38] :
      ( k1_funct_1(A_2,'#skF_4'(A_2,k2_relat_1(A_2),C_38)) = C_38
      | ~ r2_hidden(C_38,k2_relat_1(A_2))
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_10,plain,(
    ! [A_2,C_38] :
      ( r2_hidden('#skF_4'(A_2,k2_relat_1(A_2),C_38),k1_relat_1(A_2))
      | ~ r2_hidden(C_38,k2_relat_1(A_2))
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_28,plain,(
    ! [A_43] :
      ( v1_relat_1(k2_funct_1(A_43))
      | ~ v1_funct_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_40,plain,(
    v2_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_65,plain,(
    ! [A_54] :
      ( k4_relat_1(A_54) = k2_funct_1(A_54)
      | ~ v2_funct_1(A_54)
      | ~ v1_funct_1(A_54)
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_68,plain,
    ( k4_relat_1('#skF_6') = k2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_65])).

tff(c_71,plain,(
    k4_relat_1('#skF_6') = k2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_68])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_relat_1(k4_relat_1(A_1)) = k2_relat_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_76,plain,
    ( k1_relat_1(k2_funct_1('#skF_6')) = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_4])).

tff(c_83,plain,(
    k1_relat_1(k2_funct_1('#skF_6')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_76])).

tff(c_2,plain,(
    ! [A_1] :
      ( k2_relat_1(k4_relat_1(A_1)) = k1_relat_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_79,plain,
    ( k2_relat_1(k2_funct_1('#skF_6')) = k1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_2])).

tff(c_85,plain,(
    k2_relat_1(k2_funct_1('#skF_6')) = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_79])).

tff(c_95,plain,(
    ! [A_55,D_56] :
      ( r2_hidden(k1_funct_1(A_55,D_56),k2_relat_1(A_55))
      | ~ r2_hidden(D_56,k1_relat_1(A_55))
      | ~ v1_funct_1(A_55)
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_98,plain,(
    ! [D_56] :
      ( r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),D_56),k1_relat_1('#skF_6'))
      | ~ r2_hidden(D_56,k1_relat_1(k2_funct_1('#skF_6')))
      | ~ v1_funct_1(k2_funct_1('#skF_6'))
      | ~ v1_relat_1(k2_funct_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_95])).

tff(c_102,plain,(
    ! [D_56] :
      ( r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),D_56),k1_relat_1('#skF_6'))
      | ~ r2_hidden(D_56,k2_relat_1('#skF_6'))
      | ~ v1_funct_1(k2_funct_1('#skF_6'))
      | ~ v1_relat_1(k2_funct_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_98])).

tff(c_159,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_102])).

tff(c_162,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_28,c_159])).

tff(c_166,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_162])).

tff(c_168,plain,(
    v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_26,plain,(
    ! [A_43] :
      ( v1_funct_1(k2_funct_1(A_43))
      | ~ v1_funct_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_167,plain,(
    ! [D_56] :
      ( ~ v1_funct_1(k2_funct_1('#skF_6'))
      | r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),D_56),k1_relat_1('#skF_6'))
      | ~ r2_hidden(D_56,k2_relat_1('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_169,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_167])).

tff(c_172,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_26,c_169])).

tff(c_176,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_172])).

tff(c_178,plain,(
    v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_167])).

tff(c_6,plain,(
    ! [A_2,D_41] :
      ( r2_hidden(k1_funct_1(A_2,D_41),k2_relat_1(A_2))
      | ~ r2_hidden(D_41,k1_relat_1(A_2))
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_34,plain,(
    ! [B_49,A_48] :
      ( k1_funct_1(k2_funct_1(B_49),k1_funct_1(B_49,A_48)) = A_48
      | ~ r2_hidden(A_48,k1_relat_1(B_49))
      | ~ v2_funct_1(B_49)
      | ~ v1_funct_1(B_49)
      | ~ v1_relat_1(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_177,plain,(
    ! [D_56] :
      ( r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),D_56),k1_relat_1('#skF_6'))
      | ~ r2_hidden(D_56,k2_relat_1('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_167])).

tff(c_305,plain,(
    ! [B_77,C_78,A_79] :
      ( k1_funct_1(k5_relat_1(B_77,C_78),A_79) = k1_funct_1(C_78,k1_funct_1(B_77,A_79))
      | ~ r2_hidden(A_79,k1_relat_1(B_77))
      | ~ v1_funct_1(C_78)
      | ~ v1_relat_1(C_78)
      | ~ v1_funct_1(B_77)
      | ~ v1_relat_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_320,plain,(
    ! [C_78,D_56] :
      ( k1_funct_1(k5_relat_1('#skF_6',C_78),k1_funct_1(k2_funct_1('#skF_6'),D_56)) = k1_funct_1(C_78,k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),D_56)))
      | ~ v1_funct_1(C_78)
      | ~ v1_relat_1(C_78)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | ~ r2_hidden(D_56,k2_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_177,c_305])).

tff(c_662,plain,(
    ! [C_107,D_108] :
      ( k1_funct_1(k5_relat_1('#skF_6',C_107),k1_funct_1(k2_funct_1('#skF_6'),D_108)) = k1_funct_1(C_107,k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),D_108)))
      | ~ v1_funct_1(C_107)
      | ~ v1_relat_1(C_107)
      | ~ r2_hidden(D_108,k2_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_320])).

tff(c_700,plain,(
    ! [C_107,A_48] :
      ( k1_funct_1(C_107,k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6',A_48)))) = k1_funct_1(k5_relat_1('#skF_6',C_107),A_48)
      | ~ v1_funct_1(C_107)
      | ~ v1_relat_1(C_107)
      | ~ r2_hidden(k1_funct_1('#skF_6',A_48),k2_relat_1('#skF_6'))
      | ~ r2_hidden(A_48,k1_relat_1('#skF_6'))
      | ~ v2_funct_1('#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_662])).

tff(c_1636,plain,(
    ! [C_147,A_148] :
      ( k1_funct_1(C_147,k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6',A_148)))) = k1_funct_1(k5_relat_1('#skF_6',C_147),A_148)
      | ~ v1_funct_1(C_147)
      | ~ v1_relat_1(C_147)
      | ~ r2_hidden(k1_funct_1('#skF_6',A_148),k2_relat_1('#skF_6'))
      | ~ r2_hidden(A_148,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_700])).

tff(c_1752,plain,(
    ! [C_147,A_48] :
      ( k1_funct_1(k5_relat_1('#skF_6',C_147),A_48) = k1_funct_1(C_147,k1_funct_1('#skF_6',A_48))
      | ~ v1_funct_1(C_147)
      | ~ v1_relat_1(C_147)
      | ~ r2_hidden(k1_funct_1('#skF_6',A_48),k2_relat_1('#skF_6'))
      | ~ r2_hidden(A_48,k1_relat_1('#skF_6'))
      | ~ r2_hidden(A_48,k1_relat_1('#skF_6'))
      | ~ v2_funct_1('#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1636])).

tff(c_1797,plain,(
    ! [C_149,A_150] :
      ( k1_funct_1(k5_relat_1('#skF_6',C_149),A_150) = k1_funct_1(C_149,k1_funct_1('#skF_6',A_150))
      | ~ v1_funct_1(C_149)
      | ~ v1_relat_1(C_149)
      | ~ r2_hidden(k1_funct_1('#skF_6',A_150),k2_relat_1('#skF_6'))
      | ~ r2_hidden(A_150,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_1752])).

tff(c_1807,plain,(
    ! [C_149,D_41] :
      ( k1_funct_1(k5_relat_1('#skF_6',C_149),D_41) = k1_funct_1(C_149,k1_funct_1('#skF_6',D_41))
      | ~ v1_funct_1(C_149)
      | ~ v1_relat_1(C_149)
      | ~ r2_hidden(D_41,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_6,c_1797])).

tff(c_1815,plain,(
    ! [C_151,D_152] :
      ( k1_funct_1(k5_relat_1('#skF_6',C_151),D_152) = k1_funct_1(C_151,k1_funct_1('#skF_6',D_152))
      | ~ v1_funct_1(C_151)
      | ~ v1_relat_1(C_151)
      | ~ r2_hidden(D_152,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_1807])).

tff(c_1855,plain,(
    ! [C_151,C_38] :
      ( k1_funct_1(k5_relat_1('#skF_6',C_151),'#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_38)) = k1_funct_1(C_151,k1_funct_1('#skF_6','#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_38)))
      | ~ v1_funct_1(C_151)
      | ~ v1_relat_1(C_151)
      | ~ r2_hidden(C_38,k2_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_10,c_1815])).

tff(c_2193,plain,(
    ! [C_161,C_162] :
      ( k1_funct_1(k5_relat_1('#skF_6',C_161),'#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_162)) = k1_funct_1(C_161,k1_funct_1('#skF_6','#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_162)))
      | ~ v1_funct_1(C_161)
      | ~ v1_relat_1(C_161)
      | ~ r2_hidden(C_162,k2_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_1855])).

tff(c_32,plain,(
    ! [B_49,A_48] :
      ( k1_funct_1(k5_relat_1(B_49,k2_funct_1(B_49)),A_48) = A_48
      | ~ r2_hidden(A_48,k1_relat_1(B_49))
      | ~ v2_funct_1(B_49)
      | ~ v1_funct_1(B_49)
      | ~ v1_relat_1(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2207,plain,(
    ! [C_162] :
      ( k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6','#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_162))) = '#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_162)
      | ~ r2_hidden('#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_162),k1_relat_1('#skF_6'))
      | ~ v2_funct_1('#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | ~ v1_funct_1(k2_funct_1('#skF_6'))
      | ~ v1_relat_1(k2_funct_1('#skF_6'))
      | ~ r2_hidden(C_162,k2_relat_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2193,c_32])).

tff(c_2227,plain,(
    ! [C_163] :
      ( k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6','#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_163))) = '#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_163)
      | ~ r2_hidden('#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_163),k1_relat_1('#skF_6'))
      | ~ r2_hidden(C_163,k2_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_178,c_44,c_42,c_40,c_2207])).

tff(c_2274,plain,(
    ! [C_38] :
      ( k1_funct_1(k2_funct_1('#skF_6'),C_38) = '#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_38)
      | ~ r2_hidden('#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_38),k1_relat_1('#skF_6'))
      | ~ r2_hidden(C_38,k2_relat_1('#skF_6'))
      | ~ r2_hidden(C_38,k2_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_2227])).

tff(c_2296,plain,(
    ! [C_164] :
      ( k1_funct_1(k2_funct_1('#skF_6'),C_164) = '#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_164)
      | ~ r2_hidden('#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_164),k1_relat_1('#skF_6'))
      | ~ r2_hidden(C_164,k2_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_2274])).

tff(c_2300,plain,(
    ! [C_38] :
      ( k1_funct_1(k2_funct_1('#skF_6'),C_38) = '#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_38)
      | ~ r2_hidden(C_38,k2_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_10,c_2296])).

tff(c_2304,plain,(
    ! [C_165] :
      ( k1_funct_1(k2_funct_1('#skF_6'),C_165) = '#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_165)
      | ~ r2_hidden(C_165,k2_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_2300])).

tff(c_2423,plain,(
    k1_funct_1(k2_funct_1('#skF_6'),'#skF_5') = '#skF_4'('#skF_6',k2_relat_1('#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_2304])).

tff(c_36,plain,
    ( k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6'),'#skF_5') != '#skF_5'
    | k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),'#skF_5')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_72,plain,(
    k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),'#skF_5')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_2424,plain,(
    k1_funct_1('#skF_6','#skF_4'('#skF_6',k2_relat_1('#skF_6'),'#skF_5')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2423,c_72])).

tff(c_2552,plain,
    ( ~ r2_hidden('#skF_5',k2_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_2424])).

tff(c_2556,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_38,c_2552])).

tff(c_2558,plain,(
    k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),'#skF_5')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_2562,plain,
    ( k1_relat_1(k2_funct_1('#skF_6')) = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_4])).

tff(c_2569,plain,(
    k1_relat_1(k2_funct_1('#skF_6')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2562])).

tff(c_2565,plain,
    ( k2_relat_1(k2_funct_1('#skF_6')) = k1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_2])).

tff(c_2571,plain,(
    k2_relat_1(k2_funct_1('#skF_6')) = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2565])).

tff(c_2585,plain,(
    ! [A_169,D_170] :
      ( r2_hidden(k1_funct_1(A_169,D_170),k2_relat_1(A_169))
      | ~ r2_hidden(D_170,k1_relat_1(A_169))
      | ~ v1_funct_1(A_169)
      | ~ v1_relat_1(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2591,plain,(
    ! [D_170] :
      ( r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),D_170),k1_relat_1('#skF_6'))
      | ~ r2_hidden(D_170,k1_relat_1(k2_funct_1('#skF_6')))
      | ~ v1_funct_1(k2_funct_1('#skF_6'))
      | ~ v1_relat_1(k2_funct_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2571,c_2585])).

tff(c_2597,plain,(
    ! [D_170] :
      ( r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),D_170),k1_relat_1('#skF_6'))
      | ~ r2_hidden(D_170,k2_relat_1('#skF_6'))
      | ~ v1_funct_1(k2_funct_1('#skF_6'))
      | ~ v1_relat_1(k2_funct_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2569,c_2591])).

tff(c_2683,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_2597])).

tff(c_2687,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_28,c_2683])).

tff(c_2691,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_2687])).

tff(c_2693,plain,(
    v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_2597])).

tff(c_2692,plain,(
    ! [D_170] :
      ( ~ v1_funct_1(k2_funct_1('#skF_6'))
      | r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),D_170),k1_relat_1('#skF_6'))
      | ~ r2_hidden(D_170,k2_relat_1('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_2597])).

tff(c_2694,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_2692])).

tff(c_2697,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_26,c_2694])).

tff(c_2701,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_2697])).

tff(c_2703,plain,(
    v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_2692])).

tff(c_2807,plain,(
    ! [B_191,C_192,A_193] :
      ( k1_funct_1(k5_relat_1(B_191,C_192),A_193) = k1_funct_1(C_192,k1_funct_1(B_191,A_193))
      | ~ r2_hidden(A_193,k1_relat_1(B_191))
      | ~ v1_funct_1(C_192)
      | ~ v1_relat_1(C_192)
      | ~ v1_funct_1(B_191)
      | ~ v1_relat_1(B_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2829,plain,(
    ! [C_192,A_193] :
      ( k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'),C_192),A_193) = k1_funct_1(C_192,k1_funct_1(k2_funct_1('#skF_6'),A_193))
      | ~ r2_hidden(A_193,k2_relat_1('#skF_6'))
      | ~ v1_funct_1(C_192)
      | ~ v1_relat_1(C_192)
      | ~ v1_funct_1(k2_funct_1('#skF_6'))
      | ~ v1_relat_1(k2_funct_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2569,c_2807])).

tff(c_2844,plain,(
    ! [C_194,A_195] :
      ( k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'),C_194),A_195) = k1_funct_1(C_194,k1_funct_1(k2_funct_1('#skF_6'),A_195))
      | ~ r2_hidden(A_195,k2_relat_1('#skF_6'))
      | ~ v1_funct_1(C_194)
      | ~ v1_relat_1(C_194) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2693,c_2703,c_2829])).

tff(c_2557,plain,(
    k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6'),'#skF_5') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_2868,plain,
    ( k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),'#skF_5')) != '#skF_5'
    | ~ r2_hidden('#skF_5',k2_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2844,c_2557])).

tff(c_2889,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_38,c_2558,c_2868])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:48:09 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.93/2.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.93/2.11  
% 5.93/2.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.93/2.11  %$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1
% 5.93/2.11  
% 5.93/2.11  %Foreground sorts:
% 5.93/2.11  
% 5.93/2.11  
% 5.93/2.11  %Background operators:
% 5.93/2.11  
% 5.93/2.11  
% 5.93/2.11  %Foreground operators:
% 5.93/2.11  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.93/2.11  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.93/2.11  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.93/2.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.93/2.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.93/2.11  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.93/2.11  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 5.93/2.11  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.93/2.11  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.93/2.11  tff('#skF_5', type, '#skF_5': $i).
% 5.93/2.11  tff('#skF_6', type, '#skF_6': $i).
% 5.93/2.11  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.93/2.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.93/2.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.93/2.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.93/2.11  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.93/2.11  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.93/2.11  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.93/2.11  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 5.93/2.11  
% 6.02/2.13  tff(f_100, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k2_relat_1(B))) => ((A = k1_funct_1(B, k1_funct_1(k2_funct_1(B), A))) & (A = k1_funct_1(k5_relat_1(k2_funct_1(B), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_funct_1)).
% 6.02/2.13  tff(f_46, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 6.02/2.13  tff(f_62, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 6.02/2.13  tff(f_54, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 6.02/2.13  tff(f_31, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 6.02/2.13  tff(f_87, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k1_relat_1(B))) => ((A = k1_funct_1(k2_funct_1(B), k1_funct_1(B, A))) & (A = k1_funct_1(k5_relat_1(B, k2_funct_1(B)), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_funct_1)).
% 6.02/2.13  tff(f_75, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_1)).
% 6.02/2.13  tff(c_44, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.02/2.13  tff(c_42, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.02/2.13  tff(c_38, plain, (r2_hidden('#skF_5', k2_relat_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.02/2.13  tff(c_8, plain, (![A_2, C_38]: (k1_funct_1(A_2, '#skF_4'(A_2, k2_relat_1(A_2), C_38))=C_38 | ~r2_hidden(C_38, k2_relat_1(A_2)) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.02/2.13  tff(c_10, plain, (![A_2, C_38]: (r2_hidden('#skF_4'(A_2, k2_relat_1(A_2), C_38), k1_relat_1(A_2)) | ~r2_hidden(C_38, k2_relat_1(A_2)) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.02/2.13  tff(c_28, plain, (![A_43]: (v1_relat_1(k2_funct_1(A_43)) | ~v1_funct_1(A_43) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.02/2.13  tff(c_40, plain, (v2_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.02/2.13  tff(c_65, plain, (![A_54]: (k4_relat_1(A_54)=k2_funct_1(A_54) | ~v2_funct_1(A_54) | ~v1_funct_1(A_54) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.02/2.13  tff(c_68, plain, (k4_relat_1('#skF_6')=k2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_40, c_65])).
% 6.02/2.13  tff(c_71, plain, (k4_relat_1('#skF_6')=k2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_68])).
% 6.02/2.13  tff(c_4, plain, (![A_1]: (k1_relat_1(k4_relat_1(A_1))=k2_relat_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.02/2.13  tff(c_76, plain, (k1_relat_1(k2_funct_1('#skF_6'))=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_71, c_4])).
% 6.02/2.13  tff(c_83, plain, (k1_relat_1(k2_funct_1('#skF_6'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_76])).
% 6.02/2.13  tff(c_2, plain, (![A_1]: (k2_relat_1(k4_relat_1(A_1))=k1_relat_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.02/2.13  tff(c_79, plain, (k2_relat_1(k2_funct_1('#skF_6'))=k1_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_71, c_2])).
% 6.02/2.13  tff(c_85, plain, (k2_relat_1(k2_funct_1('#skF_6'))=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_79])).
% 6.02/2.13  tff(c_95, plain, (![A_55, D_56]: (r2_hidden(k1_funct_1(A_55, D_56), k2_relat_1(A_55)) | ~r2_hidden(D_56, k1_relat_1(A_55)) | ~v1_funct_1(A_55) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.02/2.13  tff(c_98, plain, (![D_56]: (r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), D_56), k1_relat_1('#skF_6')) | ~r2_hidden(D_56, k1_relat_1(k2_funct_1('#skF_6'))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_85, c_95])).
% 6.02/2.13  tff(c_102, plain, (![D_56]: (r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), D_56), k1_relat_1('#skF_6')) | ~r2_hidden(D_56, k2_relat_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_98])).
% 6.02/2.13  tff(c_159, plain, (~v1_relat_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_102])).
% 6.02/2.13  tff(c_162, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_28, c_159])).
% 6.02/2.13  tff(c_166, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_162])).
% 6.02/2.13  tff(c_168, plain, (v1_relat_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_102])).
% 6.02/2.13  tff(c_26, plain, (![A_43]: (v1_funct_1(k2_funct_1(A_43)) | ~v1_funct_1(A_43) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.02/2.13  tff(c_167, plain, (![D_56]: (~v1_funct_1(k2_funct_1('#skF_6')) | r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), D_56), k1_relat_1('#skF_6')) | ~r2_hidden(D_56, k2_relat_1('#skF_6')))), inference(splitRight, [status(thm)], [c_102])).
% 6.02/2.13  tff(c_169, plain, (~v1_funct_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_167])).
% 6.02/2.13  tff(c_172, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_26, c_169])).
% 6.02/2.13  tff(c_176, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_172])).
% 6.02/2.13  tff(c_178, plain, (v1_funct_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_167])).
% 6.02/2.13  tff(c_6, plain, (![A_2, D_41]: (r2_hidden(k1_funct_1(A_2, D_41), k2_relat_1(A_2)) | ~r2_hidden(D_41, k1_relat_1(A_2)) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.02/2.13  tff(c_34, plain, (![B_49, A_48]: (k1_funct_1(k2_funct_1(B_49), k1_funct_1(B_49, A_48))=A_48 | ~r2_hidden(A_48, k1_relat_1(B_49)) | ~v2_funct_1(B_49) | ~v1_funct_1(B_49) | ~v1_relat_1(B_49))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.02/2.13  tff(c_177, plain, (![D_56]: (r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), D_56), k1_relat_1('#skF_6')) | ~r2_hidden(D_56, k2_relat_1('#skF_6')))), inference(splitRight, [status(thm)], [c_167])).
% 6.02/2.13  tff(c_305, plain, (![B_77, C_78, A_79]: (k1_funct_1(k5_relat_1(B_77, C_78), A_79)=k1_funct_1(C_78, k1_funct_1(B_77, A_79)) | ~r2_hidden(A_79, k1_relat_1(B_77)) | ~v1_funct_1(C_78) | ~v1_relat_1(C_78) | ~v1_funct_1(B_77) | ~v1_relat_1(B_77))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.02/2.13  tff(c_320, plain, (![C_78, D_56]: (k1_funct_1(k5_relat_1('#skF_6', C_78), k1_funct_1(k2_funct_1('#skF_6'), D_56))=k1_funct_1(C_78, k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), D_56))) | ~v1_funct_1(C_78) | ~v1_relat_1(C_78) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~r2_hidden(D_56, k2_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_177, c_305])).
% 6.02/2.13  tff(c_662, plain, (![C_107, D_108]: (k1_funct_1(k5_relat_1('#skF_6', C_107), k1_funct_1(k2_funct_1('#skF_6'), D_108))=k1_funct_1(C_107, k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), D_108))) | ~v1_funct_1(C_107) | ~v1_relat_1(C_107) | ~r2_hidden(D_108, k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_320])).
% 6.02/2.13  tff(c_700, plain, (![C_107, A_48]: (k1_funct_1(C_107, k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', A_48))))=k1_funct_1(k5_relat_1('#skF_6', C_107), A_48) | ~v1_funct_1(C_107) | ~v1_relat_1(C_107) | ~r2_hidden(k1_funct_1('#skF_6', A_48), k2_relat_1('#skF_6')) | ~r2_hidden(A_48, k1_relat_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_662])).
% 6.02/2.13  tff(c_1636, plain, (![C_147, A_148]: (k1_funct_1(C_147, k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', A_148))))=k1_funct_1(k5_relat_1('#skF_6', C_147), A_148) | ~v1_funct_1(C_147) | ~v1_relat_1(C_147) | ~r2_hidden(k1_funct_1('#skF_6', A_148), k2_relat_1('#skF_6')) | ~r2_hidden(A_148, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_700])).
% 6.02/2.13  tff(c_1752, plain, (![C_147, A_48]: (k1_funct_1(k5_relat_1('#skF_6', C_147), A_48)=k1_funct_1(C_147, k1_funct_1('#skF_6', A_48)) | ~v1_funct_1(C_147) | ~v1_relat_1(C_147) | ~r2_hidden(k1_funct_1('#skF_6', A_48), k2_relat_1('#skF_6')) | ~r2_hidden(A_48, k1_relat_1('#skF_6')) | ~r2_hidden(A_48, k1_relat_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1636])).
% 6.02/2.13  tff(c_1797, plain, (![C_149, A_150]: (k1_funct_1(k5_relat_1('#skF_6', C_149), A_150)=k1_funct_1(C_149, k1_funct_1('#skF_6', A_150)) | ~v1_funct_1(C_149) | ~v1_relat_1(C_149) | ~r2_hidden(k1_funct_1('#skF_6', A_150), k2_relat_1('#skF_6')) | ~r2_hidden(A_150, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_1752])).
% 6.02/2.13  tff(c_1807, plain, (![C_149, D_41]: (k1_funct_1(k5_relat_1('#skF_6', C_149), D_41)=k1_funct_1(C_149, k1_funct_1('#skF_6', D_41)) | ~v1_funct_1(C_149) | ~v1_relat_1(C_149) | ~r2_hidden(D_41, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_6, c_1797])).
% 6.02/2.13  tff(c_1815, plain, (![C_151, D_152]: (k1_funct_1(k5_relat_1('#skF_6', C_151), D_152)=k1_funct_1(C_151, k1_funct_1('#skF_6', D_152)) | ~v1_funct_1(C_151) | ~v1_relat_1(C_151) | ~r2_hidden(D_152, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_1807])).
% 6.02/2.13  tff(c_1855, plain, (![C_151, C_38]: (k1_funct_1(k5_relat_1('#skF_6', C_151), '#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_38))=k1_funct_1(C_151, k1_funct_1('#skF_6', '#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_38))) | ~v1_funct_1(C_151) | ~v1_relat_1(C_151) | ~r2_hidden(C_38, k2_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_10, c_1815])).
% 6.02/2.13  tff(c_2193, plain, (![C_161, C_162]: (k1_funct_1(k5_relat_1('#skF_6', C_161), '#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_162))=k1_funct_1(C_161, k1_funct_1('#skF_6', '#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_162))) | ~v1_funct_1(C_161) | ~v1_relat_1(C_161) | ~r2_hidden(C_162, k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_1855])).
% 6.02/2.13  tff(c_32, plain, (![B_49, A_48]: (k1_funct_1(k5_relat_1(B_49, k2_funct_1(B_49)), A_48)=A_48 | ~r2_hidden(A_48, k1_relat_1(B_49)) | ~v2_funct_1(B_49) | ~v1_funct_1(B_49) | ~v1_relat_1(B_49))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.02/2.13  tff(c_2207, plain, (![C_162]: (k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', '#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_162)))='#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_162) | ~r2_hidden('#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_162), k1_relat_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~r2_hidden(C_162, k2_relat_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_2193, c_32])).
% 6.02/2.13  tff(c_2227, plain, (![C_163]: (k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', '#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_163)))='#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_163) | ~r2_hidden('#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_163), k1_relat_1('#skF_6')) | ~r2_hidden(C_163, k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_168, c_178, c_44, c_42, c_40, c_2207])).
% 6.02/2.13  tff(c_2274, plain, (![C_38]: (k1_funct_1(k2_funct_1('#skF_6'), C_38)='#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_38) | ~r2_hidden('#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_38), k1_relat_1('#skF_6')) | ~r2_hidden(C_38, k2_relat_1('#skF_6')) | ~r2_hidden(C_38, k2_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_8, c_2227])).
% 6.02/2.13  tff(c_2296, plain, (![C_164]: (k1_funct_1(k2_funct_1('#skF_6'), C_164)='#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_164) | ~r2_hidden('#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_164), k1_relat_1('#skF_6')) | ~r2_hidden(C_164, k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_2274])).
% 6.02/2.13  tff(c_2300, plain, (![C_38]: (k1_funct_1(k2_funct_1('#skF_6'), C_38)='#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_38) | ~r2_hidden(C_38, k2_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_10, c_2296])).
% 6.02/2.13  tff(c_2304, plain, (![C_165]: (k1_funct_1(k2_funct_1('#skF_6'), C_165)='#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_165) | ~r2_hidden(C_165, k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_2300])).
% 6.02/2.13  tff(c_2423, plain, (k1_funct_1(k2_funct_1('#skF_6'), '#skF_5')='#skF_4'('#skF_6', k2_relat_1('#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_38, c_2304])).
% 6.02/2.13  tff(c_36, plain, (k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'), '#skF_5')!='#skF_5' | k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.02/2.13  tff(c_72, plain, (k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_36])).
% 6.02/2.13  tff(c_2424, plain, (k1_funct_1('#skF_6', '#skF_4'('#skF_6', k2_relat_1('#skF_6'), '#skF_5'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2423, c_72])).
% 6.02/2.13  tff(c_2552, plain, (~r2_hidden('#skF_5', k2_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_8, c_2424])).
% 6.02/2.13  tff(c_2556, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_38, c_2552])).
% 6.02/2.13  tff(c_2558, plain, (k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'))='#skF_5'), inference(splitRight, [status(thm)], [c_36])).
% 6.02/2.13  tff(c_2562, plain, (k1_relat_1(k2_funct_1('#skF_6'))=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_71, c_4])).
% 6.02/2.13  tff(c_2569, plain, (k1_relat_1(k2_funct_1('#skF_6'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_2562])).
% 6.02/2.13  tff(c_2565, plain, (k2_relat_1(k2_funct_1('#skF_6'))=k1_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_71, c_2])).
% 6.02/2.13  tff(c_2571, plain, (k2_relat_1(k2_funct_1('#skF_6'))=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_2565])).
% 6.02/2.13  tff(c_2585, plain, (![A_169, D_170]: (r2_hidden(k1_funct_1(A_169, D_170), k2_relat_1(A_169)) | ~r2_hidden(D_170, k1_relat_1(A_169)) | ~v1_funct_1(A_169) | ~v1_relat_1(A_169))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.02/2.13  tff(c_2591, plain, (![D_170]: (r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), D_170), k1_relat_1('#skF_6')) | ~r2_hidden(D_170, k1_relat_1(k2_funct_1('#skF_6'))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_2571, c_2585])).
% 6.02/2.13  tff(c_2597, plain, (![D_170]: (r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), D_170), k1_relat_1('#skF_6')) | ~r2_hidden(D_170, k2_relat_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_2569, c_2591])).
% 6.02/2.13  tff(c_2683, plain, (~v1_relat_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_2597])).
% 6.02/2.13  tff(c_2687, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_28, c_2683])).
% 6.02/2.13  tff(c_2691, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_2687])).
% 6.02/2.13  tff(c_2693, plain, (v1_relat_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_2597])).
% 6.02/2.13  tff(c_2692, plain, (![D_170]: (~v1_funct_1(k2_funct_1('#skF_6')) | r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), D_170), k1_relat_1('#skF_6')) | ~r2_hidden(D_170, k2_relat_1('#skF_6')))), inference(splitRight, [status(thm)], [c_2597])).
% 6.02/2.13  tff(c_2694, plain, (~v1_funct_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_2692])).
% 6.02/2.13  tff(c_2697, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_26, c_2694])).
% 6.02/2.13  tff(c_2701, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_2697])).
% 6.02/2.13  tff(c_2703, plain, (v1_funct_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_2692])).
% 6.02/2.13  tff(c_2807, plain, (![B_191, C_192, A_193]: (k1_funct_1(k5_relat_1(B_191, C_192), A_193)=k1_funct_1(C_192, k1_funct_1(B_191, A_193)) | ~r2_hidden(A_193, k1_relat_1(B_191)) | ~v1_funct_1(C_192) | ~v1_relat_1(C_192) | ~v1_funct_1(B_191) | ~v1_relat_1(B_191))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.02/2.13  tff(c_2829, plain, (![C_192, A_193]: (k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'), C_192), A_193)=k1_funct_1(C_192, k1_funct_1(k2_funct_1('#skF_6'), A_193)) | ~r2_hidden(A_193, k2_relat_1('#skF_6')) | ~v1_funct_1(C_192) | ~v1_relat_1(C_192) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_2569, c_2807])).
% 6.02/2.13  tff(c_2844, plain, (![C_194, A_195]: (k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'), C_194), A_195)=k1_funct_1(C_194, k1_funct_1(k2_funct_1('#skF_6'), A_195)) | ~r2_hidden(A_195, k2_relat_1('#skF_6')) | ~v1_funct_1(C_194) | ~v1_relat_1(C_194))), inference(demodulation, [status(thm), theory('equality')], [c_2693, c_2703, c_2829])).
% 6.02/2.13  tff(c_2557, plain, (k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'), '#skF_5')!='#skF_5'), inference(splitRight, [status(thm)], [c_36])).
% 6.02/2.13  tff(c_2868, plain, (k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'))!='#skF_5' | ~r2_hidden('#skF_5', k2_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2844, c_2557])).
% 6.02/2.13  tff(c_2889, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_38, c_2558, c_2868])).
% 6.02/2.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.02/2.13  
% 6.02/2.13  Inference rules
% 6.02/2.13  ----------------------
% 6.02/2.13  #Ref     : 1
% 6.02/2.13  #Sup     : 644
% 6.02/2.13  #Fact    : 0
% 6.02/2.13  #Define  : 0
% 6.02/2.13  #Split   : 11
% 6.02/2.13  #Chain   : 0
% 6.02/2.13  #Close   : 0
% 6.02/2.13  
% 6.02/2.13  Ordering : KBO
% 6.02/2.13  
% 6.02/2.13  Simplification rules
% 6.02/2.13  ----------------------
% 6.02/2.13  #Subsume      : 91
% 6.02/2.13  #Demod        : 895
% 6.02/2.13  #Tautology    : 155
% 6.02/2.13  #SimpNegUnit  : 3
% 6.02/2.13  #BackRed      : 12
% 6.02/2.13  
% 6.02/2.13  #Partial instantiations: 0
% 6.02/2.13  #Strategies tried      : 1
% 6.02/2.13  
% 6.02/2.13  Timing (in seconds)
% 6.02/2.13  ----------------------
% 6.02/2.13  Preprocessing        : 0.34
% 6.02/2.13  Parsing              : 0.17
% 6.02/2.13  CNF conversion       : 0.03
% 6.02/2.13  Main loop            : 1.02
% 6.02/2.13  Inferencing          : 0.36
% 6.02/2.13  Reduction            : 0.35
% 6.02/2.13  Demodulation         : 0.23
% 6.02/2.13  BG Simplification    : 0.06
% 6.02/2.13  Subsumption          : 0.19
% 6.02/2.13  Abstraction          : 0.08
% 6.02/2.13  MUC search           : 0.00
% 6.02/2.13  Cooper               : 0.00
% 6.02/2.13  Total                : 1.40
% 6.02/2.13  Index Insertion      : 0.00
% 6.02/2.13  Index Deletion       : 0.00
% 6.02/2.13  Index Matching       : 0.00
% 6.02/2.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
