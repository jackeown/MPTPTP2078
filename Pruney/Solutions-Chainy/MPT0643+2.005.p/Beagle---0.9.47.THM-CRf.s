%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:40 EST 2020

% Result     : Theorem 11.11s
% Output     : CNFRefutation 11.33s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 127 expanded)
%              Number of leaves         :   30 (  64 expanded)
%              Depth                    :   10
%              Number of atoms          :  150 ( 473 expanded)
%              Number of equality atoms :   39 ( 160 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_7 > #skF_11 > #skF_3 > #skF_10 > #skF_5 > #skF_8 > #skF_9 > #skF_2 > #skF_1 > #skF_6 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_110,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ! [C] :
            ( ( v1_relat_1(C)
              & v1_funct_1(C) )
           => ( ( k1_relat_1(B) = A
                & k1_relat_1(C) = A
                & r1_tarski(k2_relat_1(C),A)
                & v2_funct_1(B)
                & k5_relat_1(C,B) = B )
             => C = k6_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_funct_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_47,axiom,(
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

tff(f_75,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
           => k1_funct_1(k5_relat_1(C,B),A) = k1_funct_1(B,k1_funct_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_1)).

tff(f_62,axiom,(
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

tff(c_46,plain,(
    k6_relat_1('#skF_9') != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_60,plain,(
    v1_relat_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_58,plain,(
    v1_funct_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_54,plain,(
    k1_relat_1('#skF_11') = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_13445,plain,(
    ! [B_632] :
      ( k1_funct_1(B_632,'#skF_8'(k1_relat_1(B_632),B_632)) != '#skF_8'(k1_relat_1(B_632),B_632)
      | k6_relat_1(k1_relat_1(B_632)) = B_632
      | ~ v1_funct_1(B_632)
      | ~ v1_relat_1(B_632) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_13448,plain,
    ( k1_funct_1('#skF_11','#skF_8'('#skF_9','#skF_11')) != '#skF_8'(k1_relat_1('#skF_11'),'#skF_11')
    | k6_relat_1(k1_relat_1('#skF_11')) = '#skF_11'
    | ~ v1_funct_1('#skF_11')
    | ~ v1_relat_1('#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_13445])).

tff(c_13453,plain,
    ( k1_funct_1('#skF_11','#skF_8'('#skF_9','#skF_11')) != '#skF_8'('#skF_9','#skF_11')
    | k6_relat_1('#skF_9') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_54,c_13448])).

tff(c_13454,plain,(
    k1_funct_1('#skF_11','#skF_8'('#skF_9','#skF_11')) != '#skF_8'('#skF_9','#skF_11') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_13453])).

tff(c_78,plain,(
    ! [A_65,B_66] :
      ( r2_hidden('#skF_1'(A_65,B_66),A_65)
      | r1_tarski(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_83,plain,(
    ! [A_65] : r1_tarski(A_65,A_65) ),
    inference(resolution,[status(thm)],[c_78,c_4])).

tff(c_150,plain,(
    ! [B_85] :
      ( r2_hidden('#skF_8'(k1_relat_1(B_85),B_85),k1_relat_1(B_85))
      | k6_relat_1(k1_relat_1(B_85)) = B_85
      | ~ v1_funct_1(B_85)
      | ~ v1_relat_1(B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_155,plain,
    ( r2_hidden('#skF_8'('#skF_9','#skF_11'),k1_relat_1('#skF_11'))
    | k6_relat_1(k1_relat_1('#skF_11')) = '#skF_11'
    | ~ v1_funct_1('#skF_11')
    | ~ v1_relat_1('#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_150])).

tff(c_167,plain,
    ( r2_hidden('#skF_8'('#skF_9','#skF_11'),'#skF_9')
    | k6_relat_1('#skF_9') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_54,c_155])).

tff(c_168,plain,(
    r2_hidden('#skF_8'('#skF_9','#skF_11'),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_167])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_178,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_8'('#skF_9','#skF_11'),B_2)
      | ~ r1_tarski('#skF_9',B_2) ) ),
    inference(resolution,[status(thm)],[c_168,c_2])).

tff(c_52,plain,(
    r1_tarski(k2_relat_1('#skF_11'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_138,plain,(
    ! [A_79,D_80] :
      ( r2_hidden(k1_funct_1(A_79,D_80),k2_relat_1(A_79))
      | ~ r2_hidden(D_80,k1_relat_1(A_79))
      | ~ v1_funct_1(A_79)
      | ~ v1_relat_1(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_13417,plain,(
    ! [A_625,D_626,B_627] :
      ( r2_hidden(k1_funct_1(A_625,D_626),B_627)
      | ~ r1_tarski(k2_relat_1(A_625),B_627)
      | ~ r2_hidden(D_626,k1_relat_1(A_625))
      | ~ v1_funct_1(A_625)
      | ~ v1_relat_1(A_625) ) ),
    inference(resolution,[status(thm)],[c_138,c_2])).

tff(c_13590,plain,(
    ! [A_679,D_680,B_681,B_682] :
      ( r2_hidden(k1_funct_1(A_679,D_680),B_681)
      | ~ r1_tarski(B_682,B_681)
      | ~ r1_tarski(k2_relat_1(A_679),B_682)
      | ~ r2_hidden(D_680,k1_relat_1(A_679))
      | ~ v1_funct_1(A_679)
      | ~ v1_relat_1(A_679) ) ),
    inference(resolution,[status(thm)],[c_13417,c_2])).

tff(c_13597,plain,(
    ! [A_683,D_684] :
      ( r2_hidden(k1_funct_1(A_683,D_684),'#skF_9')
      | ~ r1_tarski(k2_relat_1(A_683),k2_relat_1('#skF_11'))
      | ~ r2_hidden(D_684,k1_relat_1(A_683))
      | ~ v1_funct_1(A_683)
      | ~ v1_relat_1(A_683) ) ),
    inference(resolution,[status(thm)],[c_52,c_13590])).

tff(c_13600,plain,(
    ! [D_684] :
      ( r2_hidden(k1_funct_1('#skF_11',D_684),'#skF_9')
      | ~ r2_hidden(D_684,k1_relat_1('#skF_11'))
      | ~ v1_funct_1('#skF_11')
      | ~ v1_relat_1('#skF_11') ) ),
    inference(resolution,[status(thm)],[c_83,c_13597])).

tff(c_13603,plain,(
    ! [D_684] :
      ( r2_hidden(k1_funct_1('#skF_11',D_684),'#skF_9')
      | ~ r2_hidden(D_684,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_13600])).

tff(c_64,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_62,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_50,plain,(
    v2_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_56,plain,(
    k1_relat_1('#skF_10') = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_48,plain,(
    k5_relat_1('#skF_11','#skF_10') = '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_14222,plain,(
    ! [C_715,B_716,A_717] :
      ( k1_funct_1(k5_relat_1(C_715,B_716),A_717) = k1_funct_1(B_716,k1_funct_1(C_715,A_717))
      | ~ r2_hidden(A_717,k1_relat_1(k5_relat_1(C_715,B_716)))
      | ~ v1_funct_1(C_715)
      | ~ v1_relat_1(C_715)
      | ~ v1_funct_1(B_716)
      | ~ v1_relat_1(B_716) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_14321,plain,(
    ! [A_717] :
      ( k1_funct_1(k5_relat_1('#skF_11','#skF_10'),A_717) = k1_funct_1('#skF_10',k1_funct_1('#skF_11',A_717))
      | ~ r2_hidden(A_717,k1_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_11')
      | ~ v1_relat_1('#skF_11')
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_14222])).

tff(c_14348,plain,(
    ! [A_718] :
      ( k1_funct_1('#skF_10',k1_funct_1('#skF_11',A_718)) = k1_funct_1('#skF_10',A_718)
      | ~ r2_hidden(A_718,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_58,c_56,c_48,c_14321])).

tff(c_26,plain,(
    ! [C_52,B_51,A_46] :
      ( C_52 = B_51
      | k1_funct_1(A_46,C_52) != k1_funct_1(A_46,B_51)
      | ~ r2_hidden(C_52,k1_relat_1(A_46))
      | ~ r2_hidden(B_51,k1_relat_1(A_46))
      | ~ v2_funct_1(A_46)
      | ~ v1_funct_1(A_46)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_14358,plain,(
    ! [A_718,B_51] :
      ( k1_funct_1('#skF_11',A_718) = B_51
      | k1_funct_1('#skF_10',B_51) != k1_funct_1('#skF_10',A_718)
      | ~ r2_hidden(k1_funct_1('#skF_11',A_718),k1_relat_1('#skF_10'))
      | ~ r2_hidden(B_51,k1_relat_1('#skF_10'))
      | ~ v2_funct_1('#skF_10')
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10')
      | ~ r2_hidden(A_718,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14348,c_26])).

tff(c_14384,plain,(
    ! [A_718,B_51] :
      ( k1_funct_1('#skF_11',A_718) = B_51
      | k1_funct_1('#skF_10',B_51) != k1_funct_1('#skF_10',A_718)
      | ~ r2_hidden(k1_funct_1('#skF_11',A_718),'#skF_9')
      | ~ r2_hidden(B_51,'#skF_9')
      | ~ r2_hidden(A_718,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_50,c_56,c_56,c_14358])).

tff(c_17307,plain,(
    ! [A_966] :
      ( k1_funct_1('#skF_11',A_966) = A_966
      | ~ r2_hidden(k1_funct_1('#skF_11',A_966),'#skF_9')
      | ~ r2_hidden(A_966,'#skF_9')
      | ~ r2_hidden(A_966,'#skF_9') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_14384])).

tff(c_17362,plain,(
    ! [D_967] :
      ( k1_funct_1('#skF_11',D_967) = D_967
      | ~ r2_hidden(D_967,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_13603,c_17307])).

tff(c_17570,plain,
    ( k1_funct_1('#skF_11','#skF_8'('#skF_9','#skF_11')) = '#skF_8'('#skF_9','#skF_11')
    | ~ r1_tarski('#skF_9','#skF_9') ),
    inference(resolution,[status(thm)],[c_178,c_17362])).

tff(c_17675,plain,(
    k1_funct_1('#skF_11','#skF_8'('#skF_9','#skF_11')) = '#skF_8'('#skF_9','#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_17570])).

tff(c_17677,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13454,c_17675])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:01:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.11/3.95  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.11/3.96  
% 11.11/3.96  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.11/3.96  %$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_7 > #skF_11 > #skF_3 > #skF_10 > #skF_5 > #skF_8 > #skF_9 > #skF_2 > #skF_1 > #skF_6 > #skF_4
% 11.11/3.96  
% 11.11/3.96  %Foreground sorts:
% 11.11/3.96  
% 11.11/3.96  
% 11.11/3.96  %Background operators:
% 11.11/3.96  
% 11.11/3.96  
% 11.11/3.96  %Foreground operators:
% 11.11/3.96  tff('#skF_7', type, '#skF_7': $i > $i).
% 11.11/3.96  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.11/3.96  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 11.11/3.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.11/3.96  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.11/3.96  tff('#skF_11', type, '#skF_11': $i).
% 11.11/3.96  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 11.11/3.96  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 11.11/3.96  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.11/3.96  tff('#skF_10', type, '#skF_10': $i).
% 11.11/3.96  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.11/3.96  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 11.11/3.96  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 11.11/3.96  tff('#skF_9', type, '#skF_9': $i).
% 11.11/3.96  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 11.11/3.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.11/3.96  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.11/3.96  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 11.11/3.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.11/3.96  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 11.11/3.96  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.11/3.96  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.11/3.96  tff('#skF_6', type, '#skF_6': $i > $i).
% 11.11/3.96  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 11.11/3.96  
% 11.33/3.97  tff(f_110, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((((((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) & r1_tarski(k2_relat_1(C), A)) & v2_funct_1(B)) & (k5_relat_1(C, B) = B)) => (C = k6_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_funct_1)).
% 11.33/3.97  tff(f_88, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_funct_1)).
% 11.33/3.97  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 11.33/3.97  tff(f_47, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 11.33/3.97  tff(f_75, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) => (k1_funct_1(k5_relat_1(C, B), A) = k1_funct_1(B, k1_funct_1(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_funct_1)).
% 11.33/3.97  tff(f_62, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_funct_1)).
% 11.33/3.97  tff(c_46, plain, (k6_relat_1('#skF_9')!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_110])).
% 11.33/3.97  tff(c_60, plain, (v1_relat_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_110])).
% 11.33/3.97  tff(c_58, plain, (v1_funct_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_110])).
% 11.33/3.97  tff(c_54, plain, (k1_relat_1('#skF_11')='#skF_9'), inference(cnfTransformation, [status(thm)], [f_110])).
% 11.33/3.97  tff(c_13445, plain, (![B_632]: (k1_funct_1(B_632, '#skF_8'(k1_relat_1(B_632), B_632))!='#skF_8'(k1_relat_1(B_632), B_632) | k6_relat_1(k1_relat_1(B_632))=B_632 | ~v1_funct_1(B_632) | ~v1_relat_1(B_632))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.33/3.97  tff(c_13448, plain, (k1_funct_1('#skF_11', '#skF_8'('#skF_9', '#skF_11'))!='#skF_8'(k1_relat_1('#skF_11'), '#skF_11') | k6_relat_1(k1_relat_1('#skF_11'))='#skF_11' | ~v1_funct_1('#skF_11') | ~v1_relat_1('#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_54, c_13445])).
% 11.33/3.97  tff(c_13453, plain, (k1_funct_1('#skF_11', '#skF_8'('#skF_9', '#skF_11'))!='#skF_8'('#skF_9', '#skF_11') | k6_relat_1('#skF_9')='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_54, c_13448])).
% 11.33/3.97  tff(c_13454, plain, (k1_funct_1('#skF_11', '#skF_8'('#skF_9', '#skF_11'))!='#skF_8'('#skF_9', '#skF_11')), inference(negUnitSimplification, [status(thm)], [c_46, c_13453])).
% 11.33/3.97  tff(c_78, plain, (![A_65, B_66]: (r2_hidden('#skF_1'(A_65, B_66), A_65) | r1_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.33/3.97  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.33/3.97  tff(c_83, plain, (![A_65]: (r1_tarski(A_65, A_65))), inference(resolution, [status(thm)], [c_78, c_4])).
% 11.33/3.97  tff(c_150, plain, (![B_85]: (r2_hidden('#skF_8'(k1_relat_1(B_85), B_85), k1_relat_1(B_85)) | k6_relat_1(k1_relat_1(B_85))=B_85 | ~v1_funct_1(B_85) | ~v1_relat_1(B_85))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.33/3.97  tff(c_155, plain, (r2_hidden('#skF_8'('#skF_9', '#skF_11'), k1_relat_1('#skF_11')) | k6_relat_1(k1_relat_1('#skF_11'))='#skF_11' | ~v1_funct_1('#skF_11') | ~v1_relat_1('#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_54, c_150])).
% 11.33/3.97  tff(c_167, plain, (r2_hidden('#skF_8'('#skF_9', '#skF_11'), '#skF_9') | k6_relat_1('#skF_9')='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_54, c_155])).
% 11.33/3.97  tff(c_168, plain, (r2_hidden('#skF_8'('#skF_9', '#skF_11'), '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_46, c_167])).
% 11.33/3.97  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.33/3.97  tff(c_178, plain, (![B_2]: (r2_hidden('#skF_8'('#skF_9', '#skF_11'), B_2) | ~r1_tarski('#skF_9', B_2))), inference(resolution, [status(thm)], [c_168, c_2])).
% 11.33/3.97  tff(c_52, plain, (r1_tarski(k2_relat_1('#skF_11'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_110])).
% 11.33/3.97  tff(c_138, plain, (![A_79, D_80]: (r2_hidden(k1_funct_1(A_79, D_80), k2_relat_1(A_79)) | ~r2_hidden(D_80, k1_relat_1(A_79)) | ~v1_funct_1(A_79) | ~v1_relat_1(A_79))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.33/3.97  tff(c_13417, plain, (![A_625, D_626, B_627]: (r2_hidden(k1_funct_1(A_625, D_626), B_627) | ~r1_tarski(k2_relat_1(A_625), B_627) | ~r2_hidden(D_626, k1_relat_1(A_625)) | ~v1_funct_1(A_625) | ~v1_relat_1(A_625))), inference(resolution, [status(thm)], [c_138, c_2])).
% 11.33/3.97  tff(c_13590, plain, (![A_679, D_680, B_681, B_682]: (r2_hidden(k1_funct_1(A_679, D_680), B_681) | ~r1_tarski(B_682, B_681) | ~r1_tarski(k2_relat_1(A_679), B_682) | ~r2_hidden(D_680, k1_relat_1(A_679)) | ~v1_funct_1(A_679) | ~v1_relat_1(A_679))), inference(resolution, [status(thm)], [c_13417, c_2])).
% 11.33/3.97  tff(c_13597, plain, (![A_683, D_684]: (r2_hidden(k1_funct_1(A_683, D_684), '#skF_9') | ~r1_tarski(k2_relat_1(A_683), k2_relat_1('#skF_11')) | ~r2_hidden(D_684, k1_relat_1(A_683)) | ~v1_funct_1(A_683) | ~v1_relat_1(A_683))), inference(resolution, [status(thm)], [c_52, c_13590])).
% 11.33/3.97  tff(c_13600, plain, (![D_684]: (r2_hidden(k1_funct_1('#skF_11', D_684), '#skF_9') | ~r2_hidden(D_684, k1_relat_1('#skF_11')) | ~v1_funct_1('#skF_11') | ~v1_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_83, c_13597])).
% 11.33/3.97  tff(c_13603, plain, (![D_684]: (r2_hidden(k1_funct_1('#skF_11', D_684), '#skF_9') | ~r2_hidden(D_684, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_13600])).
% 11.33/3.97  tff(c_64, plain, (v1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_110])).
% 11.33/3.97  tff(c_62, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_110])).
% 11.33/3.97  tff(c_50, plain, (v2_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_110])).
% 11.33/3.97  tff(c_56, plain, (k1_relat_1('#skF_10')='#skF_9'), inference(cnfTransformation, [status(thm)], [f_110])).
% 11.33/3.97  tff(c_48, plain, (k5_relat_1('#skF_11', '#skF_10')='#skF_10'), inference(cnfTransformation, [status(thm)], [f_110])).
% 11.33/3.97  tff(c_14222, plain, (![C_715, B_716, A_717]: (k1_funct_1(k5_relat_1(C_715, B_716), A_717)=k1_funct_1(B_716, k1_funct_1(C_715, A_717)) | ~r2_hidden(A_717, k1_relat_1(k5_relat_1(C_715, B_716))) | ~v1_funct_1(C_715) | ~v1_relat_1(C_715) | ~v1_funct_1(B_716) | ~v1_relat_1(B_716))), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.33/3.97  tff(c_14321, plain, (![A_717]: (k1_funct_1(k5_relat_1('#skF_11', '#skF_10'), A_717)=k1_funct_1('#skF_10', k1_funct_1('#skF_11', A_717)) | ~r2_hidden(A_717, k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_11') | ~v1_relat_1('#skF_11') | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_48, c_14222])).
% 11.33/3.97  tff(c_14348, plain, (![A_718]: (k1_funct_1('#skF_10', k1_funct_1('#skF_11', A_718))=k1_funct_1('#skF_10', A_718) | ~r2_hidden(A_718, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_58, c_56, c_48, c_14321])).
% 11.33/3.97  tff(c_26, plain, (![C_52, B_51, A_46]: (C_52=B_51 | k1_funct_1(A_46, C_52)!=k1_funct_1(A_46, B_51) | ~r2_hidden(C_52, k1_relat_1(A_46)) | ~r2_hidden(B_51, k1_relat_1(A_46)) | ~v2_funct_1(A_46) | ~v1_funct_1(A_46) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.33/3.97  tff(c_14358, plain, (![A_718, B_51]: (k1_funct_1('#skF_11', A_718)=B_51 | k1_funct_1('#skF_10', B_51)!=k1_funct_1('#skF_10', A_718) | ~r2_hidden(k1_funct_1('#skF_11', A_718), k1_relat_1('#skF_10')) | ~r2_hidden(B_51, k1_relat_1('#skF_10')) | ~v2_funct_1('#skF_10') | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | ~r2_hidden(A_718, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_14348, c_26])).
% 11.33/3.97  tff(c_14384, plain, (![A_718, B_51]: (k1_funct_1('#skF_11', A_718)=B_51 | k1_funct_1('#skF_10', B_51)!=k1_funct_1('#skF_10', A_718) | ~r2_hidden(k1_funct_1('#skF_11', A_718), '#skF_9') | ~r2_hidden(B_51, '#skF_9') | ~r2_hidden(A_718, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_50, c_56, c_56, c_14358])).
% 11.33/3.97  tff(c_17307, plain, (![A_966]: (k1_funct_1('#skF_11', A_966)=A_966 | ~r2_hidden(k1_funct_1('#skF_11', A_966), '#skF_9') | ~r2_hidden(A_966, '#skF_9') | ~r2_hidden(A_966, '#skF_9'))), inference(reflexivity, [status(thm), theory('equality')], [c_14384])).
% 11.33/3.97  tff(c_17362, plain, (![D_967]: (k1_funct_1('#skF_11', D_967)=D_967 | ~r2_hidden(D_967, '#skF_9'))), inference(resolution, [status(thm)], [c_13603, c_17307])).
% 11.33/3.97  tff(c_17570, plain, (k1_funct_1('#skF_11', '#skF_8'('#skF_9', '#skF_11'))='#skF_8'('#skF_9', '#skF_11') | ~r1_tarski('#skF_9', '#skF_9')), inference(resolution, [status(thm)], [c_178, c_17362])).
% 11.33/3.97  tff(c_17675, plain, (k1_funct_1('#skF_11', '#skF_8'('#skF_9', '#skF_11'))='#skF_8'('#skF_9', '#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_17570])).
% 11.33/3.97  tff(c_17677, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13454, c_17675])).
% 11.33/3.97  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.33/3.97  
% 11.33/3.97  Inference rules
% 11.33/3.97  ----------------------
% 11.33/3.97  #Ref     : 15
% 11.33/3.97  #Sup     : 3767
% 11.33/3.97  #Fact    : 0
% 11.33/3.97  #Define  : 0
% 11.33/3.97  #Split   : 14
% 11.33/3.97  #Chain   : 0
% 11.33/3.97  #Close   : 0
% 11.33/3.97  
% 11.33/3.97  Ordering : KBO
% 11.33/3.97  
% 11.33/3.97  Simplification rules
% 11.33/3.97  ----------------------
% 11.33/3.97  #Subsume      : 980
% 11.33/3.97  #Demod        : 5066
% 11.33/3.97  #Tautology    : 987
% 11.33/3.97  #SimpNegUnit  : 86
% 11.33/3.97  #BackRed      : 198
% 11.33/3.97  
% 11.33/3.97  #Partial instantiations: 0
% 11.33/3.97  #Strategies tried      : 1
% 11.33/3.97  
% 11.33/3.97  Timing (in seconds)
% 11.33/3.97  ----------------------
% 11.33/3.98  Preprocessing        : 0.34
% 11.33/3.98  Parsing              : 0.17
% 11.33/3.98  CNF conversion       : 0.03
% 11.33/3.98  Main loop            : 2.88
% 11.33/3.98  Inferencing          : 0.94
% 11.33/3.98  Reduction            : 0.88
% 11.33/3.98  Demodulation         : 0.61
% 11.33/3.98  BG Simplification    : 0.11
% 11.33/3.98  Subsumption          : 0.73
% 11.33/3.98  Abstraction          : 0.15
% 11.33/3.98  MUC search           : 0.00
% 11.33/3.98  Cooper               : 0.00
% 11.33/3.98  Total                : 3.24
% 11.33/3.98  Index Insertion      : 0.00
% 11.33/3.98  Index Deletion       : 0.00
% 11.33/3.98  Index Matching       : 0.00
% 11.33/3.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
