%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:41 EST 2020

% Result     : Theorem 10.90s
% Output     : CNFRefutation 10.90s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 127 expanded)
%              Number of leaves         :   30 (  63 expanded)
%              Depth                    :   12
%              Number of atoms          :  158 ( 470 expanded)
%              Number of equality atoms :   41 ( 157 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_funct_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

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

tff(c_11901,plain,(
    ! [B_555] :
      ( k1_funct_1(B_555,'#skF_8'(k1_relat_1(B_555),B_555)) != '#skF_8'(k1_relat_1(B_555),B_555)
      | k6_relat_1(k1_relat_1(B_555)) = B_555
      | ~ v1_funct_1(B_555)
      | ~ v1_relat_1(B_555) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_11904,plain,
    ( k1_funct_1('#skF_11','#skF_8'('#skF_9','#skF_11')) != '#skF_8'(k1_relat_1('#skF_11'),'#skF_11')
    | k6_relat_1(k1_relat_1('#skF_11')) = '#skF_11'
    | ~ v1_funct_1('#skF_11')
    | ~ v1_relat_1('#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_11901])).

tff(c_11909,plain,
    ( k1_funct_1('#skF_11','#skF_8'('#skF_9','#skF_11')) != '#skF_8'('#skF_9','#skF_11')
    | k6_relat_1('#skF_9') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_54,c_11904])).

tff(c_11910,plain,(
    k1_funct_1('#skF_11','#skF_8'('#skF_9','#skF_11')) != '#skF_8'('#skF_9','#skF_11') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_11909])).

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

tff(c_11796,plain,(
    ! [A_532,D_533,B_534] :
      ( r2_hidden(k1_funct_1(A_532,D_533),B_534)
      | ~ r1_tarski(k2_relat_1(A_532),B_534)
      | ~ r2_hidden(D_533,k1_relat_1(A_532))
      | ~ v1_funct_1(A_532)
      | ~ v1_relat_1(A_532) ) ),
    inference(resolution,[status(thm)],[c_138,c_2])).

tff(c_12023,plain,(
    ! [A_593,D_594,B_595,B_596] :
      ( r2_hidden(k1_funct_1(A_593,D_594),B_595)
      | ~ r1_tarski(B_596,B_595)
      | ~ r1_tarski(k2_relat_1(A_593),B_596)
      | ~ r2_hidden(D_594,k1_relat_1(A_593))
      | ~ v1_funct_1(A_593)
      | ~ v1_relat_1(A_593) ) ),
    inference(resolution,[status(thm)],[c_11796,c_2])).

tff(c_12260,plain,(
    ! [A_604,D_605] :
      ( r2_hidden(k1_funct_1(A_604,D_605),'#skF_9')
      | ~ r1_tarski(k2_relat_1(A_604),k2_relat_1('#skF_11'))
      | ~ r2_hidden(D_605,k1_relat_1(A_604))
      | ~ v1_funct_1(A_604)
      | ~ v1_relat_1(A_604) ) ),
    inference(resolution,[status(thm)],[c_52,c_12023])).

tff(c_12263,plain,(
    ! [D_605] :
      ( r2_hidden(k1_funct_1('#skF_11',D_605),'#skF_9')
      | ~ r2_hidden(D_605,k1_relat_1('#skF_11'))
      | ~ v1_funct_1('#skF_11')
      | ~ v1_relat_1('#skF_11') ) ),
    inference(resolution,[status(thm)],[c_83,c_12260])).

tff(c_12266,plain,(
    ! [D_605] :
      ( r2_hidden(k1_funct_1('#skF_11',D_605),'#skF_9')
      | ~ r2_hidden(D_605,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_12263])).

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

tff(c_12030,plain,(
    ! [B_597,C_598,A_599] :
      ( k1_funct_1(k5_relat_1(B_597,C_598),A_599) = k1_funct_1(C_598,k1_funct_1(B_597,A_599))
      | ~ r2_hidden(A_599,k1_relat_1(B_597))
      | ~ v1_funct_1(C_598)
      | ~ v1_relat_1(C_598)
      | ~ v1_funct_1(B_597)
      | ~ v1_relat_1(B_597) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_12120,plain,(
    ! [C_598,A_599] :
      ( k1_funct_1(k5_relat_1('#skF_11',C_598),A_599) = k1_funct_1(C_598,k1_funct_1('#skF_11',A_599))
      | ~ r2_hidden(A_599,'#skF_9')
      | ~ v1_funct_1(C_598)
      | ~ v1_relat_1(C_598)
      | ~ v1_funct_1('#skF_11')
      | ~ v1_relat_1('#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_12030])).

tff(c_12158,plain,(
    ! [C_600,A_601] :
      ( k1_funct_1(k5_relat_1('#skF_11',C_600),A_601) = k1_funct_1(C_600,k1_funct_1('#skF_11',A_601))
      | ~ r2_hidden(A_601,'#skF_9')
      | ~ v1_funct_1(C_600)
      | ~ v1_relat_1(C_600) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_12120])).

tff(c_12201,plain,(
    ! [A_601] :
      ( k1_funct_1('#skF_10',k1_funct_1('#skF_11',A_601)) = k1_funct_1('#skF_10',A_601)
      | ~ r2_hidden(A_601,'#skF_9')
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_12158])).

tff(c_12205,plain,(
    ! [A_601] :
      ( k1_funct_1('#skF_10',k1_funct_1('#skF_11',A_601)) = k1_funct_1('#skF_10',A_601)
      | ~ r2_hidden(A_601,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_12201])).

tff(c_15923,plain,(
    ! [C_883,B_884,A_885] :
      ( C_883 = B_884
      | k1_funct_1(A_885,C_883) != k1_funct_1(A_885,B_884)
      | ~ r2_hidden(C_883,k1_relat_1(A_885))
      | ~ r2_hidden(B_884,k1_relat_1(A_885))
      | ~ v2_funct_1(A_885)
      | ~ v1_funct_1(A_885)
      | ~ v1_relat_1(A_885) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_15931,plain,(
    ! [A_601,C_883] :
      ( k1_funct_1('#skF_11',A_601) = C_883
      | k1_funct_1('#skF_10',C_883) != k1_funct_1('#skF_10',A_601)
      | ~ r2_hidden(C_883,k1_relat_1('#skF_10'))
      | ~ r2_hidden(k1_funct_1('#skF_11',A_601),k1_relat_1('#skF_10'))
      | ~ v2_funct_1('#skF_10')
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10')
      | ~ r2_hidden(A_601,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12205,c_15923])).

tff(c_15951,plain,(
    ! [A_601,C_883] :
      ( k1_funct_1('#skF_11',A_601) = C_883
      | k1_funct_1('#skF_10',C_883) != k1_funct_1('#skF_10',A_601)
      | ~ r2_hidden(C_883,'#skF_9')
      | ~ r2_hidden(k1_funct_1('#skF_11',A_601),'#skF_9')
      | ~ r2_hidden(A_601,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_50,c_56,c_56,c_15931])).

tff(c_16449,plain,(
    ! [A_940] :
      ( k1_funct_1('#skF_11',A_940) = A_940
      | ~ r2_hidden(A_940,'#skF_9')
      | ~ r2_hidden(k1_funct_1('#skF_11',A_940),'#skF_9')
      | ~ r2_hidden(A_940,'#skF_9') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_15951])).

tff(c_16482,plain,(
    ! [D_941] :
      ( k1_funct_1('#skF_11',D_941) = D_941
      | ~ r2_hidden(D_941,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_12266,c_16449])).

tff(c_16636,plain,
    ( k1_funct_1('#skF_11','#skF_8'('#skF_9','#skF_11')) = '#skF_8'('#skF_9','#skF_11')
    | ~ r1_tarski('#skF_9','#skF_9') ),
    inference(resolution,[status(thm)],[c_178,c_16482])).

tff(c_16720,plain,(
    k1_funct_1('#skF_11','#skF_8'('#skF_9','#skF_11')) = '#skF_8'('#skF_9','#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_16636])).

tff(c_16722,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11910,c_16720])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:56:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.90/3.88  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.90/3.89  
% 10.90/3.89  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.90/3.89  %$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_7 > #skF_11 > #skF_3 > #skF_10 > #skF_5 > #skF_8 > #skF_9 > #skF_2 > #skF_1 > #skF_6 > #skF_4
% 10.90/3.89  
% 10.90/3.89  %Foreground sorts:
% 10.90/3.89  
% 10.90/3.89  
% 10.90/3.89  %Background operators:
% 10.90/3.89  
% 10.90/3.89  
% 10.90/3.89  %Foreground operators:
% 10.90/3.89  tff('#skF_7', type, '#skF_7': $i > $i).
% 10.90/3.89  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.90/3.89  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 10.90/3.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.90/3.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.90/3.89  tff('#skF_11', type, '#skF_11': $i).
% 10.90/3.89  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 10.90/3.89  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 10.90/3.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.90/3.89  tff('#skF_10', type, '#skF_10': $i).
% 10.90/3.89  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.90/3.89  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 10.90/3.89  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 10.90/3.89  tff('#skF_9', type, '#skF_9': $i).
% 10.90/3.89  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 10.90/3.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.90/3.89  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.90/3.89  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 10.90/3.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.90/3.89  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 10.90/3.89  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.90/3.89  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.90/3.89  tff('#skF_6', type, '#skF_6': $i > $i).
% 10.90/3.89  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 10.90/3.89  
% 10.90/3.90  tff(f_110, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((((((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) & r1_tarski(k2_relat_1(C), A)) & v2_funct_1(B)) & (k5_relat_1(C, B) = B)) => (C = k6_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_funct_1)).
% 10.90/3.90  tff(f_88, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_funct_1)).
% 10.90/3.90  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 10.90/3.90  tff(f_47, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 10.90/3.90  tff(f_75, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_1)).
% 10.90/3.90  tff(f_62, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_funct_1)).
% 10.90/3.90  tff(c_46, plain, (k6_relat_1('#skF_9')!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_110])).
% 10.90/3.90  tff(c_60, plain, (v1_relat_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_110])).
% 10.90/3.90  tff(c_58, plain, (v1_funct_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_110])).
% 10.90/3.90  tff(c_54, plain, (k1_relat_1('#skF_11')='#skF_9'), inference(cnfTransformation, [status(thm)], [f_110])).
% 10.90/3.90  tff(c_11901, plain, (![B_555]: (k1_funct_1(B_555, '#skF_8'(k1_relat_1(B_555), B_555))!='#skF_8'(k1_relat_1(B_555), B_555) | k6_relat_1(k1_relat_1(B_555))=B_555 | ~v1_funct_1(B_555) | ~v1_relat_1(B_555))), inference(cnfTransformation, [status(thm)], [f_88])).
% 10.90/3.90  tff(c_11904, plain, (k1_funct_1('#skF_11', '#skF_8'('#skF_9', '#skF_11'))!='#skF_8'(k1_relat_1('#skF_11'), '#skF_11') | k6_relat_1(k1_relat_1('#skF_11'))='#skF_11' | ~v1_funct_1('#skF_11') | ~v1_relat_1('#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_54, c_11901])).
% 10.90/3.90  tff(c_11909, plain, (k1_funct_1('#skF_11', '#skF_8'('#skF_9', '#skF_11'))!='#skF_8'('#skF_9', '#skF_11') | k6_relat_1('#skF_9')='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_54, c_11904])).
% 10.90/3.90  tff(c_11910, plain, (k1_funct_1('#skF_11', '#skF_8'('#skF_9', '#skF_11'))!='#skF_8'('#skF_9', '#skF_11')), inference(negUnitSimplification, [status(thm)], [c_46, c_11909])).
% 10.90/3.90  tff(c_78, plain, (![A_65, B_66]: (r2_hidden('#skF_1'(A_65, B_66), A_65) | r1_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.90/3.90  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.90/3.90  tff(c_83, plain, (![A_65]: (r1_tarski(A_65, A_65))), inference(resolution, [status(thm)], [c_78, c_4])).
% 10.90/3.90  tff(c_150, plain, (![B_85]: (r2_hidden('#skF_8'(k1_relat_1(B_85), B_85), k1_relat_1(B_85)) | k6_relat_1(k1_relat_1(B_85))=B_85 | ~v1_funct_1(B_85) | ~v1_relat_1(B_85))), inference(cnfTransformation, [status(thm)], [f_88])).
% 10.90/3.90  tff(c_155, plain, (r2_hidden('#skF_8'('#skF_9', '#skF_11'), k1_relat_1('#skF_11')) | k6_relat_1(k1_relat_1('#skF_11'))='#skF_11' | ~v1_funct_1('#skF_11') | ~v1_relat_1('#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_54, c_150])).
% 10.90/3.90  tff(c_167, plain, (r2_hidden('#skF_8'('#skF_9', '#skF_11'), '#skF_9') | k6_relat_1('#skF_9')='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_54, c_155])).
% 10.90/3.90  tff(c_168, plain, (r2_hidden('#skF_8'('#skF_9', '#skF_11'), '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_46, c_167])).
% 10.90/3.90  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.90/3.90  tff(c_178, plain, (![B_2]: (r2_hidden('#skF_8'('#skF_9', '#skF_11'), B_2) | ~r1_tarski('#skF_9', B_2))), inference(resolution, [status(thm)], [c_168, c_2])).
% 10.90/3.90  tff(c_52, plain, (r1_tarski(k2_relat_1('#skF_11'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_110])).
% 10.90/3.90  tff(c_138, plain, (![A_79, D_80]: (r2_hidden(k1_funct_1(A_79, D_80), k2_relat_1(A_79)) | ~r2_hidden(D_80, k1_relat_1(A_79)) | ~v1_funct_1(A_79) | ~v1_relat_1(A_79))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.90/3.90  tff(c_11796, plain, (![A_532, D_533, B_534]: (r2_hidden(k1_funct_1(A_532, D_533), B_534) | ~r1_tarski(k2_relat_1(A_532), B_534) | ~r2_hidden(D_533, k1_relat_1(A_532)) | ~v1_funct_1(A_532) | ~v1_relat_1(A_532))), inference(resolution, [status(thm)], [c_138, c_2])).
% 10.90/3.90  tff(c_12023, plain, (![A_593, D_594, B_595, B_596]: (r2_hidden(k1_funct_1(A_593, D_594), B_595) | ~r1_tarski(B_596, B_595) | ~r1_tarski(k2_relat_1(A_593), B_596) | ~r2_hidden(D_594, k1_relat_1(A_593)) | ~v1_funct_1(A_593) | ~v1_relat_1(A_593))), inference(resolution, [status(thm)], [c_11796, c_2])).
% 10.90/3.90  tff(c_12260, plain, (![A_604, D_605]: (r2_hidden(k1_funct_1(A_604, D_605), '#skF_9') | ~r1_tarski(k2_relat_1(A_604), k2_relat_1('#skF_11')) | ~r2_hidden(D_605, k1_relat_1(A_604)) | ~v1_funct_1(A_604) | ~v1_relat_1(A_604))), inference(resolution, [status(thm)], [c_52, c_12023])).
% 10.90/3.90  tff(c_12263, plain, (![D_605]: (r2_hidden(k1_funct_1('#skF_11', D_605), '#skF_9') | ~r2_hidden(D_605, k1_relat_1('#skF_11')) | ~v1_funct_1('#skF_11') | ~v1_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_83, c_12260])).
% 10.90/3.90  tff(c_12266, plain, (![D_605]: (r2_hidden(k1_funct_1('#skF_11', D_605), '#skF_9') | ~r2_hidden(D_605, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_12263])).
% 10.90/3.90  tff(c_64, plain, (v1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_110])).
% 10.90/3.90  tff(c_62, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_110])).
% 10.90/3.90  tff(c_50, plain, (v2_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_110])).
% 10.90/3.90  tff(c_56, plain, (k1_relat_1('#skF_10')='#skF_9'), inference(cnfTransformation, [status(thm)], [f_110])).
% 10.90/3.90  tff(c_48, plain, (k5_relat_1('#skF_11', '#skF_10')='#skF_10'), inference(cnfTransformation, [status(thm)], [f_110])).
% 10.90/3.90  tff(c_12030, plain, (![B_597, C_598, A_599]: (k1_funct_1(k5_relat_1(B_597, C_598), A_599)=k1_funct_1(C_598, k1_funct_1(B_597, A_599)) | ~r2_hidden(A_599, k1_relat_1(B_597)) | ~v1_funct_1(C_598) | ~v1_relat_1(C_598) | ~v1_funct_1(B_597) | ~v1_relat_1(B_597))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.90/3.90  tff(c_12120, plain, (![C_598, A_599]: (k1_funct_1(k5_relat_1('#skF_11', C_598), A_599)=k1_funct_1(C_598, k1_funct_1('#skF_11', A_599)) | ~r2_hidden(A_599, '#skF_9') | ~v1_funct_1(C_598) | ~v1_relat_1(C_598) | ~v1_funct_1('#skF_11') | ~v1_relat_1('#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_54, c_12030])).
% 10.90/3.90  tff(c_12158, plain, (![C_600, A_601]: (k1_funct_1(k5_relat_1('#skF_11', C_600), A_601)=k1_funct_1(C_600, k1_funct_1('#skF_11', A_601)) | ~r2_hidden(A_601, '#skF_9') | ~v1_funct_1(C_600) | ~v1_relat_1(C_600))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_12120])).
% 10.90/3.90  tff(c_12201, plain, (![A_601]: (k1_funct_1('#skF_10', k1_funct_1('#skF_11', A_601))=k1_funct_1('#skF_10', A_601) | ~r2_hidden(A_601, '#skF_9') | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_48, c_12158])).
% 10.90/3.90  tff(c_12205, plain, (![A_601]: (k1_funct_1('#skF_10', k1_funct_1('#skF_11', A_601))=k1_funct_1('#skF_10', A_601) | ~r2_hidden(A_601, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_12201])).
% 10.90/3.90  tff(c_15923, plain, (![C_883, B_884, A_885]: (C_883=B_884 | k1_funct_1(A_885, C_883)!=k1_funct_1(A_885, B_884) | ~r2_hidden(C_883, k1_relat_1(A_885)) | ~r2_hidden(B_884, k1_relat_1(A_885)) | ~v2_funct_1(A_885) | ~v1_funct_1(A_885) | ~v1_relat_1(A_885))), inference(cnfTransformation, [status(thm)], [f_62])).
% 10.90/3.90  tff(c_15931, plain, (![A_601, C_883]: (k1_funct_1('#skF_11', A_601)=C_883 | k1_funct_1('#skF_10', C_883)!=k1_funct_1('#skF_10', A_601) | ~r2_hidden(C_883, k1_relat_1('#skF_10')) | ~r2_hidden(k1_funct_1('#skF_11', A_601), k1_relat_1('#skF_10')) | ~v2_funct_1('#skF_10') | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | ~r2_hidden(A_601, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_12205, c_15923])).
% 10.90/3.90  tff(c_15951, plain, (![A_601, C_883]: (k1_funct_1('#skF_11', A_601)=C_883 | k1_funct_1('#skF_10', C_883)!=k1_funct_1('#skF_10', A_601) | ~r2_hidden(C_883, '#skF_9') | ~r2_hidden(k1_funct_1('#skF_11', A_601), '#skF_9') | ~r2_hidden(A_601, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_50, c_56, c_56, c_15931])).
% 10.90/3.90  tff(c_16449, plain, (![A_940]: (k1_funct_1('#skF_11', A_940)=A_940 | ~r2_hidden(A_940, '#skF_9') | ~r2_hidden(k1_funct_1('#skF_11', A_940), '#skF_9') | ~r2_hidden(A_940, '#skF_9'))), inference(reflexivity, [status(thm), theory('equality')], [c_15951])).
% 10.90/3.90  tff(c_16482, plain, (![D_941]: (k1_funct_1('#skF_11', D_941)=D_941 | ~r2_hidden(D_941, '#skF_9'))), inference(resolution, [status(thm)], [c_12266, c_16449])).
% 10.90/3.90  tff(c_16636, plain, (k1_funct_1('#skF_11', '#skF_8'('#skF_9', '#skF_11'))='#skF_8'('#skF_9', '#skF_11') | ~r1_tarski('#skF_9', '#skF_9')), inference(resolution, [status(thm)], [c_178, c_16482])).
% 10.90/3.90  tff(c_16720, plain, (k1_funct_1('#skF_11', '#skF_8'('#skF_9', '#skF_11'))='#skF_8'('#skF_9', '#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_16636])).
% 10.90/3.90  tff(c_16722, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11910, c_16720])).
% 10.90/3.90  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.90/3.90  
% 10.90/3.90  Inference rules
% 10.90/3.90  ----------------------
% 10.90/3.90  #Ref     : 11
% 10.90/3.90  #Sup     : 3700
% 10.90/3.90  #Fact    : 0
% 10.90/3.90  #Define  : 0
% 10.90/3.90  #Split   : 13
% 10.90/3.90  #Chain   : 0
% 10.90/3.90  #Close   : 0
% 10.90/3.90  
% 10.90/3.90  Ordering : KBO
% 10.90/3.90  
% 10.90/3.90  Simplification rules
% 10.90/3.90  ----------------------
% 10.90/3.90  #Subsume      : 1063
% 10.90/3.90  #Demod        : 4173
% 10.90/3.90  #Tautology    : 870
% 10.90/3.90  #SimpNegUnit  : 80
% 10.90/3.90  #BackRed      : 174
% 10.90/3.90  
% 10.90/3.90  #Partial instantiations: 0
% 10.90/3.90  #Strategies tried      : 1
% 10.90/3.90  
% 10.90/3.90  Timing (in seconds)
% 10.90/3.90  ----------------------
% 10.90/3.91  Preprocessing        : 0.33
% 10.90/3.91  Parsing              : 0.16
% 10.90/3.91  CNF conversion       : 0.03
% 10.90/3.91  Main loop            : 2.79
% 10.90/3.91  Inferencing          : 0.93
% 10.90/3.91  Reduction            : 0.86
% 10.90/3.91  Demodulation         : 0.58
% 10.90/3.91  BG Simplification    : 0.11
% 10.90/3.91  Subsumption          : 0.68
% 10.90/3.91  Abstraction          : 0.15
% 10.90/3.91  MUC search           : 0.00
% 10.90/3.91  Cooper               : 0.00
% 10.90/3.91  Total                : 3.14
% 10.90/3.91  Index Insertion      : 0.00
% 10.90/3.91  Index Deletion       : 0.00
% 10.90/3.91  Index Matching       : 0.00
% 10.90/3.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
