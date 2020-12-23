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
% DateTime   : Thu Dec  3 10:03:46 EST 2020

% Result     : Theorem 3.91s
% Output     : CNFRefutation 4.09s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 486 expanded)
%              Number of leaves         :   25 ( 176 expanded)
%              Depth                    :   15
%              Number of atoms          :  249 (1883 expanded)
%              Number of equality atoms :   32 ( 401 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1

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

tff(f_111,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( ( v2_funct_1(B)
            & r2_hidden(A,k2_relat_1(B)) )
         => ( A = k1_funct_1(B,k1_funct_1(k2_funct_1(B),A))
            & A = k1_funct_1(k5_relat_1(k2_funct_1(B),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_funct_1)).

tff(f_40,axiom,(
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

tff(f_98,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( v2_funct_1(B)
          & r2_hidden(A,k1_relat_1(B)) )
       => ( A = k1_funct_1(k2_funct_1(B),k1_funct_1(B,A))
          & A = k1_funct_1(k5_relat_1(B,k2_funct_1(B)),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).

tff(f_48,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_86,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
          <=> ( r2_hidden(A,k1_relat_1(C))
              & r2_hidden(k1_funct_1(C,A),k1_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
           => k1_funct_1(k5_relat_1(C,B),A) = k1_funct_1(B,k1_funct_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_1)).

tff(c_48,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_46,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_42,plain,(
    r2_hidden('#skF_5',k2_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_4,plain,(
    ! [A_1,C_37] :
      ( k1_funct_1(A_1,'#skF_4'(A_1,k2_relat_1(A_1),C_37)) = C_37
      | ~ r2_hidden(C_37,k2_relat_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_44,plain,(
    v2_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_6,plain,(
    ! [A_1,C_37] :
      ( r2_hidden('#skF_4'(A_1,k2_relat_1(A_1),C_37),k1_relat_1(A_1))
      | ~ r2_hidden(C_37,k2_relat_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_97,plain,(
    ! [B_65,A_66] :
      ( k1_funct_1(k2_funct_1(B_65),k1_funct_1(B_65,A_66)) = A_66
      | ~ r2_hidden(A_66,k1_relat_1(B_65))
      | ~ v2_funct_1(B_65)
      | ~ v1_funct_1(B_65)
      | ~ v1_relat_1(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_641,plain,(
    ! [A_124,C_125] :
      ( k1_funct_1(k2_funct_1(A_124),C_125) = '#skF_4'(A_124,k2_relat_1(A_124),C_125)
      | ~ r2_hidden('#skF_4'(A_124,k2_relat_1(A_124),C_125),k1_relat_1(A_124))
      | ~ v2_funct_1(A_124)
      | ~ v1_funct_1(A_124)
      | ~ v1_relat_1(A_124)
      | ~ r2_hidden(C_125,k2_relat_1(A_124))
      | ~ v1_funct_1(A_124)
      | ~ v1_relat_1(A_124) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_97])).

tff(c_657,plain,(
    ! [A_126,C_127] :
      ( k1_funct_1(k2_funct_1(A_126),C_127) = '#skF_4'(A_126,k2_relat_1(A_126),C_127)
      | ~ v2_funct_1(A_126)
      | ~ r2_hidden(C_127,k2_relat_1(A_126))
      | ~ v1_funct_1(A_126)
      | ~ v1_relat_1(A_126) ) ),
    inference(resolution,[status(thm)],[c_6,c_641])).

tff(c_687,plain,
    ( k1_funct_1(k2_funct_1('#skF_6'),'#skF_5') = '#skF_4'('#skF_6',k2_relat_1('#skF_6'),'#skF_5')
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_657])).

tff(c_700,plain,(
    k1_funct_1(k2_funct_1('#skF_6'),'#skF_5') = '#skF_4'('#skF_6',k2_relat_1('#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_687])).

tff(c_40,plain,
    ( k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6'),'#skF_5') != '#skF_5'
    | k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),'#skF_5')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_73,plain,(
    k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),'#skF_5')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_701,plain,(
    k1_funct_1('#skF_6','#skF_4'('#skF_6',k2_relat_1('#skF_6'),'#skF_5')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_700,c_73])).

tff(c_732,plain,
    ( ~ r2_hidden('#skF_5',k2_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_701])).

tff(c_736,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_42,c_732])).

tff(c_737,plain,(
    k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6'),'#skF_5') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_22,plain,(
    ! [A_41] :
      ( v1_relat_1(k2_funct_1(A_41))
      | ~ v1_funct_1(A_41)
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_34,plain,(
    ! [A_50] :
      ( k1_relat_1(k2_funct_1(A_50)) = k2_relat_1(A_50)
      | ~ v2_funct_1(A_50)
      | ~ v1_funct_1(A_50)
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_26,plain,(
    ! [C_45,A_42,B_43] :
      ( r2_hidden(k1_funct_1(C_45,A_42),k1_relat_1(B_43))
      | ~ r2_hidden(A_42,k1_relat_1(k5_relat_1(C_45,B_43)))
      | ~ v1_funct_1(C_45)
      | ~ v1_relat_1(C_45)
      | ~ v1_funct_1(B_43)
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_738,plain,(
    k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),'#skF_5')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_874,plain,(
    ! [C_145,A_146,B_147] :
      ( r2_hidden(k1_funct_1(C_145,A_146),k1_relat_1(B_147))
      | ~ r2_hidden(A_146,k1_relat_1(k5_relat_1(C_145,B_147)))
      | ~ v1_funct_1(C_145)
      | ~ v1_relat_1(C_145)
      | ~ v1_funct_1(B_147)
      | ~ v1_relat_1(B_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_893,plain,(
    ! [B_147] :
      ( r2_hidden('#skF_5',k1_relat_1(B_147))
      | ~ r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),'#skF_5'),k1_relat_1(k5_relat_1('#skF_6',B_147)))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | ~ v1_funct_1(B_147)
      | ~ v1_relat_1(B_147) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_738,c_874])).

tff(c_900,plain,(
    ! [B_148] :
      ( r2_hidden('#skF_5',k1_relat_1(B_148))
      | ~ r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),'#skF_5'),k1_relat_1(k5_relat_1('#skF_6',B_148)))
      | ~ v1_funct_1(B_148)
      | ~ v1_relat_1(B_148) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_893])).

tff(c_904,plain,(
    ! [B_148] :
      ( r2_hidden('#skF_5',k1_relat_1(B_148))
      | ~ v1_funct_1(B_148)
      | ~ v1_relat_1(B_148)
      | ~ r2_hidden('#skF_5',k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'),k5_relat_1('#skF_6',B_148))))
      | ~ v1_funct_1(k2_funct_1('#skF_6'))
      | ~ v1_relat_1(k2_funct_1('#skF_6'))
      | ~ v1_funct_1(k5_relat_1('#skF_6',B_148))
      | ~ v1_relat_1(k5_relat_1('#skF_6',B_148)) ) ),
    inference(resolution,[status(thm)],[c_26,c_900])).

tff(c_926,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_904])).

tff(c_929,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_22,c_926])).

tff(c_933,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_929])).

tff(c_935,plain,(
    v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_904])).

tff(c_20,plain,(
    ! [A_41] :
      ( v1_funct_1(k2_funct_1(A_41))
      | ~ v1_funct_1(A_41)
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_906,plain,(
    ! [A_152,B_153,D_154] :
      ( r2_hidden('#skF_2'(A_152,B_153),k1_relat_1(A_152))
      | k1_funct_1(A_152,D_154) != '#skF_3'(A_152,B_153)
      | ~ r2_hidden(D_154,k1_relat_1(A_152))
      | k2_relat_1(A_152) = B_153
      | ~ v1_funct_1(A_152)
      | ~ v1_relat_1(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_916,plain,(
    ! [B_153] :
      ( r2_hidden('#skF_2'('#skF_6',B_153),k1_relat_1('#skF_6'))
      | '#skF_3'('#skF_6',B_153) != '#skF_5'
      | ~ r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),'#skF_5'),k1_relat_1('#skF_6'))
      | k2_relat_1('#skF_6') = B_153
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_738,c_906])).

tff(c_918,plain,(
    ! [B_153] :
      ( r2_hidden('#skF_2'('#skF_6',B_153),k1_relat_1('#skF_6'))
      | '#skF_3'('#skF_6',B_153) != '#skF_5'
      | ~ r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),'#skF_5'),k1_relat_1('#skF_6'))
      | k2_relat_1('#skF_6') = B_153 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_916])).

tff(c_919,plain,(
    ~ r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),'#skF_5'),k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_918])).

tff(c_922,plain,
    ( ~ r2_hidden('#skF_5',k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6')))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_26,c_919])).

tff(c_925,plain,
    ( ~ r2_hidden('#skF_5',k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6')))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_922])).

tff(c_937,plain,
    ( ~ r2_hidden('#skF_5',k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6')))
    | ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_935,c_925])).

tff(c_938,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_937])).

tff(c_941,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_20,c_938])).

tff(c_945,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_941])).

tff(c_947,plain,(
    v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_937])).

tff(c_32,plain,(
    ! [A_50] :
      ( k2_relat_1(k2_funct_1(A_50)) = k1_relat_1(A_50)
      | ~ v2_funct_1(A_50)
      | ~ v1_funct_1(A_50)
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_69,plain,(
    ! [A_57,D_58] :
      ( r2_hidden(k1_funct_1(A_57,D_58),k2_relat_1(A_57))
      | ~ r2_hidden(D_58,k1_relat_1(A_57))
      | ~ v1_funct_1(A_57)
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1004,plain,(
    ! [A_161,D_162] :
      ( r2_hidden(k1_funct_1(k2_funct_1(A_161),D_162),k1_relat_1(A_161))
      | ~ r2_hidden(D_162,k1_relat_1(k2_funct_1(A_161)))
      | ~ v1_funct_1(k2_funct_1(A_161))
      | ~ v1_relat_1(k2_funct_1(A_161))
      | ~ v2_funct_1(A_161)
      | ~ v1_funct_1(A_161)
      | ~ v1_relat_1(A_161) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_69])).

tff(c_1014,plain,
    ( ~ r2_hidden('#skF_5',k1_relat_1(k2_funct_1('#skF_6')))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1004,c_919])).

tff(c_1037,plain,(
    ~ r2_hidden('#skF_5',k1_relat_1(k2_funct_1('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_935,c_947,c_1014])).

tff(c_1044,plain,
    ( ~ r2_hidden('#skF_5',k2_relat_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1037])).

tff(c_1047,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_1044])).

tff(c_1049,plain,(
    r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),'#skF_5'),k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_918])).

tff(c_1051,plain,(
    ! [A_165,C_166,B_167] :
      ( r2_hidden(A_165,k1_relat_1(k5_relat_1(C_166,B_167)))
      | ~ r2_hidden(k1_funct_1(C_166,A_165),k1_relat_1(B_167))
      | ~ r2_hidden(A_165,k1_relat_1(C_166))
      | ~ v1_funct_1(C_166)
      | ~ v1_relat_1(C_166)
      | ~ v1_funct_1(B_167)
      | ~ v1_relat_1(B_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1054,plain,
    ( r2_hidden('#skF_5',k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6')))
    | ~ r2_hidden('#skF_5',k1_relat_1(k2_funct_1('#skF_6')))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1049,c_1051])).

tff(c_1078,plain,
    ( r2_hidden('#skF_5',k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6')))
    | ~ r2_hidden('#skF_5',k1_relat_1(k2_funct_1('#skF_6')))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_1054])).

tff(c_1134,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1078])).

tff(c_1137,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_22,c_1134])).

tff(c_1141,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_1137])).

tff(c_1143,plain,(
    v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_1078])).

tff(c_1145,plain,(
    ! [B_148] :
      ( r2_hidden('#skF_5',k1_relat_1(B_148))
      | ~ v1_funct_1(B_148)
      | ~ v1_relat_1(B_148)
      | ~ r2_hidden('#skF_5',k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'),k5_relat_1('#skF_6',B_148))))
      | ~ v1_funct_1(k2_funct_1('#skF_6'))
      | ~ v1_funct_1(k5_relat_1('#skF_6',B_148))
      | ~ v1_relat_1(k5_relat_1('#skF_6',B_148)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1143,c_904])).

tff(c_1146,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1145])).

tff(c_1149,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_20,c_1146])).

tff(c_1153,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_1149])).

tff(c_1155,plain,(
    v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_1145])).

tff(c_1142,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ r2_hidden('#skF_5',k1_relat_1(k2_funct_1('#skF_6')))
    | r2_hidden('#skF_5',k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_1078])).

tff(c_1157,plain,
    ( ~ r2_hidden('#skF_5',k1_relat_1(k2_funct_1('#skF_6')))
    | r2_hidden('#skF_5',k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1155,c_1142])).

tff(c_1158,plain,(
    ~ r2_hidden('#skF_5',k1_relat_1(k2_funct_1('#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_1157])).

tff(c_1161,plain,
    ( ~ r2_hidden('#skF_5',k2_relat_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1158])).

tff(c_1164,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_1161])).

tff(c_1165,plain,(
    r2_hidden('#skF_5',k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_1157])).

tff(c_30,plain,(
    ! [C_49,B_47,A_46] :
      ( k1_funct_1(k5_relat_1(C_49,B_47),A_46) = k1_funct_1(B_47,k1_funct_1(C_49,A_46))
      | ~ r2_hidden(A_46,k1_relat_1(k5_relat_1(C_49,B_47)))
      | ~ v1_funct_1(C_49)
      | ~ v1_relat_1(C_49)
      | ~ v1_funct_1(B_47)
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1187,plain,
    ( k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6'),'#skF_5') = k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),'#skF_5'))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1165,c_30])).

tff(c_1193,plain,(
    k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6'),'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_1143,c_1155,c_738,c_1187])).

tff(c_1195,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_737,c_1193])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:18:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.91/1.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.91/1.67  
% 3.91/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.91/1.68  %$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1
% 3.91/1.68  
% 3.91/1.68  %Foreground sorts:
% 3.91/1.68  
% 3.91/1.68  
% 3.91/1.68  %Background operators:
% 3.91/1.68  
% 3.91/1.68  
% 3.91/1.68  %Foreground operators:
% 3.91/1.68  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.91/1.68  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.91/1.68  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.91/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.91/1.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.91/1.68  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.91/1.68  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.91/1.68  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.91/1.68  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.91/1.68  tff('#skF_5', type, '#skF_5': $i).
% 3.91/1.68  tff('#skF_6', type, '#skF_6': $i).
% 3.91/1.68  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.91/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.91/1.68  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.91/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.91/1.68  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.91/1.68  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.91/1.68  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.91/1.68  
% 4.09/1.69  tff(f_111, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k2_relat_1(B))) => ((A = k1_funct_1(B, k1_funct_1(k2_funct_1(B), A))) & (A = k1_funct_1(k5_relat_1(k2_funct_1(B), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_funct_1)).
% 4.09/1.69  tff(f_40, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 4.09/1.69  tff(f_98, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k1_relat_1(B))) => ((A = k1_funct_1(k2_funct_1(B), k1_funct_1(B, A))) & (A = k1_funct_1(k5_relat_1(B, k2_funct_1(B)), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_funct_1)).
% 4.09/1.69  tff(f_48, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 4.09/1.69  tff(f_86, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 4.09/1.69  tff(f_63, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) <=> (r2_hidden(A, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, A), k1_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_funct_1)).
% 4.09/1.69  tff(f_76, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) => (k1_funct_1(k5_relat_1(C, B), A) = k1_funct_1(B, k1_funct_1(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_funct_1)).
% 4.09/1.69  tff(c_48, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.09/1.69  tff(c_46, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.09/1.69  tff(c_42, plain, (r2_hidden('#skF_5', k2_relat_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.09/1.69  tff(c_4, plain, (![A_1, C_37]: (k1_funct_1(A_1, '#skF_4'(A_1, k2_relat_1(A_1), C_37))=C_37 | ~r2_hidden(C_37, k2_relat_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.09/1.69  tff(c_44, plain, (v2_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.09/1.69  tff(c_6, plain, (![A_1, C_37]: (r2_hidden('#skF_4'(A_1, k2_relat_1(A_1), C_37), k1_relat_1(A_1)) | ~r2_hidden(C_37, k2_relat_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.09/1.69  tff(c_97, plain, (![B_65, A_66]: (k1_funct_1(k2_funct_1(B_65), k1_funct_1(B_65, A_66))=A_66 | ~r2_hidden(A_66, k1_relat_1(B_65)) | ~v2_funct_1(B_65) | ~v1_funct_1(B_65) | ~v1_relat_1(B_65))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.09/1.69  tff(c_641, plain, (![A_124, C_125]: (k1_funct_1(k2_funct_1(A_124), C_125)='#skF_4'(A_124, k2_relat_1(A_124), C_125) | ~r2_hidden('#skF_4'(A_124, k2_relat_1(A_124), C_125), k1_relat_1(A_124)) | ~v2_funct_1(A_124) | ~v1_funct_1(A_124) | ~v1_relat_1(A_124) | ~r2_hidden(C_125, k2_relat_1(A_124)) | ~v1_funct_1(A_124) | ~v1_relat_1(A_124))), inference(superposition, [status(thm), theory('equality')], [c_4, c_97])).
% 4.09/1.69  tff(c_657, plain, (![A_126, C_127]: (k1_funct_1(k2_funct_1(A_126), C_127)='#skF_4'(A_126, k2_relat_1(A_126), C_127) | ~v2_funct_1(A_126) | ~r2_hidden(C_127, k2_relat_1(A_126)) | ~v1_funct_1(A_126) | ~v1_relat_1(A_126))), inference(resolution, [status(thm)], [c_6, c_641])).
% 4.09/1.69  tff(c_687, plain, (k1_funct_1(k2_funct_1('#skF_6'), '#skF_5')='#skF_4'('#skF_6', k2_relat_1('#skF_6'), '#skF_5') | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_42, c_657])).
% 4.09/1.69  tff(c_700, plain, (k1_funct_1(k2_funct_1('#skF_6'), '#skF_5')='#skF_4'('#skF_6', k2_relat_1('#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_687])).
% 4.09/1.69  tff(c_40, plain, (k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'), '#skF_5')!='#skF_5' | k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.09/1.69  tff(c_73, plain, (k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_40])).
% 4.09/1.69  tff(c_701, plain, (k1_funct_1('#skF_6', '#skF_4'('#skF_6', k2_relat_1('#skF_6'), '#skF_5'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_700, c_73])).
% 4.09/1.69  tff(c_732, plain, (~r2_hidden('#skF_5', k2_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_4, c_701])).
% 4.09/1.69  tff(c_736, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_42, c_732])).
% 4.09/1.69  tff(c_737, plain, (k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'), '#skF_5')!='#skF_5'), inference(splitRight, [status(thm)], [c_40])).
% 4.09/1.69  tff(c_22, plain, (![A_41]: (v1_relat_1(k2_funct_1(A_41)) | ~v1_funct_1(A_41) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.09/1.69  tff(c_34, plain, (![A_50]: (k1_relat_1(k2_funct_1(A_50))=k2_relat_1(A_50) | ~v2_funct_1(A_50) | ~v1_funct_1(A_50) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.09/1.69  tff(c_26, plain, (![C_45, A_42, B_43]: (r2_hidden(k1_funct_1(C_45, A_42), k1_relat_1(B_43)) | ~r2_hidden(A_42, k1_relat_1(k5_relat_1(C_45, B_43))) | ~v1_funct_1(C_45) | ~v1_relat_1(C_45) | ~v1_funct_1(B_43) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.09/1.69  tff(c_738, plain, (k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'))='#skF_5'), inference(splitRight, [status(thm)], [c_40])).
% 4.09/1.69  tff(c_874, plain, (![C_145, A_146, B_147]: (r2_hidden(k1_funct_1(C_145, A_146), k1_relat_1(B_147)) | ~r2_hidden(A_146, k1_relat_1(k5_relat_1(C_145, B_147))) | ~v1_funct_1(C_145) | ~v1_relat_1(C_145) | ~v1_funct_1(B_147) | ~v1_relat_1(B_147))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.09/1.69  tff(c_893, plain, (![B_147]: (r2_hidden('#skF_5', k1_relat_1(B_147)) | ~r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'), k1_relat_1(k5_relat_1('#skF_6', B_147))) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_funct_1(B_147) | ~v1_relat_1(B_147))), inference(superposition, [status(thm), theory('equality')], [c_738, c_874])).
% 4.09/1.69  tff(c_900, plain, (![B_148]: (r2_hidden('#skF_5', k1_relat_1(B_148)) | ~r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'), k1_relat_1(k5_relat_1('#skF_6', B_148))) | ~v1_funct_1(B_148) | ~v1_relat_1(B_148))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_893])).
% 4.09/1.69  tff(c_904, plain, (![B_148]: (r2_hidden('#skF_5', k1_relat_1(B_148)) | ~v1_funct_1(B_148) | ~v1_relat_1(B_148) | ~r2_hidden('#skF_5', k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'), k5_relat_1('#skF_6', B_148)))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v1_funct_1(k5_relat_1('#skF_6', B_148)) | ~v1_relat_1(k5_relat_1('#skF_6', B_148)))), inference(resolution, [status(thm)], [c_26, c_900])).
% 4.09/1.69  tff(c_926, plain, (~v1_relat_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_904])).
% 4.09/1.69  tff(c_929, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_22, c_926])).
% 4.09/1.69  tff(c_933, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_929])).
% 4.09/1.69  tff(c_935, plain, (v1_relat_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_904])).
% 4.09/1.69  tff(c_20, plain, (![A_41]: (v1_funct_1(k2_funct_1(A_41)) | ~v1_funct_1(A_41) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.09/1.69  tff(c_906, plain, (![A_152, B_153, D_154]: (r2_hidden('#skF_2'(A_152, B_153), k1_relat_1(A_152)) | k1_funct_1(A_152, D_154)!='#skF_3'(A_152, B_153) | ~r2_hidden(D_154, k1_relat_1(A_152)) | k2_relat_1(A_152)=B_153 | ~v1_funct_1(A_152) | ~v1_relat_1(A_152))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.09/1.69  tff(c_916, plain, (![B_153]: (r2_hidden('#skF_2'('#skF_6', B_153), k1_relat_1('#skF_6')) | '#skF_3'('#skF_6', B_153)!='#skF_5' | ~r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'), k1_relat_1('#skF_6')) | k2_relat_1('#skF_6')=B_153 | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_738, c_906])).
% 4.09/1.69  tff(c_918, plain, (![B_153]: (r2_hidden('#skF_2'('#skF_6', B_153), k1_relat_1('#skF_6')) | '#skF_3'('#skF_6', B_153)!='#skF_5' | ~r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'), k1_relat_1('#skF_6')) | k2_relat_1('#skF_6')=B_153)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_916])).
% 4.09/1.69  tff(c_919, plain, (~r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'), k1_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_918])).
% 4.09/1.69  tff(c_922, plain, (~r2_hidden('#skF_5', k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_26, c_919])).
% 4.09/1.69  tff(c_925, plain, (~r2_hidden('#skF_5', k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_922])).
% 4.09/1.69  tff(c_937, plain, (~r2_hidden('#skF_5', k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'))) | ~v1_funct_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_935, c_925])).
% 4.09/1.69  tff(c_938, plain, (~v1_funct_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_937])).
% 4.09/1.69  tff(c_941, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_20, c_938])).
% 4.09/1.69  tff(c_945, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_941])).
% 4.09/1.69  tff(c_947, plain, (v1_funct_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_937])).
% 4.09/1.69  tff(c_32, plain, (![A_50]: (k2_relat_1(k2_funct_1(A_50))=k1_relat_1(A_50) | ~v2_funct_1(A_50) | ~v1_funct_1(A_50) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.09/1.69  tff(c_69, plain, (![A_57, D_58]: (r2_hidden(k1_funct_1(A_57, D_58), k2_relat_1(A_57)) | ~r2_hidden(D_58, k1_relat_1(A_57)) | ~v1_funct_1(A_57) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.09/1.69  tff(c_1004, plain, (![A_161, D_162]: (r2_hidden(k1_funct_1(k2_funct_1(A_161), D_162), k1_relat_1(A_161)) | ~r2_hidden(D_162, k1_relat_1(k2_funct_1(A_161))) | ~v1_funct_1(k2_funct_1(A_161)) | ~v1_relat_1(k2_funct_1(A_161)) | ~v2_funct_1(A_161) | ~v1_funct_1(A_161) | ~v1_relat_1(A_161))), inference(superposition, [status(thm), theory('equality')], [c_32, c_69])).
% 4.09/1.69  tff(c_1014, plain, (~r2_hidden('#skF_5', k1_relat_1(k2_funct_1('#skF_6'))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_1004, c_919])).
% 4.09/1.69  tff(c_1037, plain, (~r2_hidden('#skF_5', k1_relat_1(k2_funct_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_935, c_947, c_1014])).
% 4.09/1.69  tff(c_1044, plain, (~r2_hidden('#skF_5', k2_relat_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_34, c_1037])).
% 4.09/1.69  tff(c_1047, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_1044])).
% 4.09/1.69  tff(c_1049, plain, (r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'), k1_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_918])).
% 4.09/1.69  tff(c_1051, plain, (![A_165, C_166, B_167]: (r2_hidden(A_165, k1_relat_1(k5_relat_1(C_166, B_167))) | ~r2_hidden(k1_funct_1(C_166, A_165), k1_relat_1(B_167)) | ~r2_hidden(A_165, k1_relat_1(C_166)) | ~v1_funct_1(C_166) | ~v1_relat_1(C_166) | ~v1_funct_1(B_167) | ~v1_relat_1(B_167))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.09/1.69  tff(c_1054, plain, (r2_hidden('#skF_5', k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'))) | ~r2_hidden('#skF_5', k1_relat_1(k2_funct_1('#skF_6'))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_1049, c_1051])).
% 4.09/1.69  tff(c_1078, plain, (r2_hidden('#skF_5', k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'))) | ~r2_hidden('#skF_5', k1_relat_1(k2_funct_1('#skF_6'))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_1054])).
% 4.09/1.69  tff(c_1134, plain, (~v1_relat_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_1078])).
% 4.09/1.69  tff(c_1137, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_22, c_1134])).
% 4.09/1.69  tff(c_1141, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_1137])).
% 4.09/1.69  tff(c_1143, plain, (v1_relat_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_1078])).
% 4.09/1.69  tff(c_1145, plain, (![B_148]: (r2_hidden('#skF_5', k1_relat_1(B_148)) | ~v1_funct_1(B_148) | ~v1_relat_1(B_148) | ~r2_hidden('#skF_5', k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'), k5_relat_1('#skF_6', B_148)))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_funct_1(k5_relat_1('#skF_6', B_148)) | ~v1_relat_1(k5_relat_1('#skF_6', B_148)))), inference(demodulation, [status(thm), theory('equality')], [c_1143, c_904])).
% 4.09/1.69  tff(c_1146, plain, (~v1_funct_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_1145])).
% 4.09/1.69  tff(c_1149, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_20, c_1146])).
% 4.09/1.69  tff(c_1153, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_1149])).
% 4.09/1.69  tff(c_1155, plain, (v1_funct_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_1145])).
% 4.09/1.69  tff(c_1142, plain, (~v1_funct_1(k2_funct_1('#skF_6')) | ~r2_hidden('#skF_5', k1_relat_1(k2_funct_1('#skF_6'))) | r2_hidden('#skF_5', k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6')))), inference(splitRight, [status(thm)], [c_1078])).
% 4.09/1.69  tff(c_1157, plain, (~r2_hidden('#skF_5', k1_relat_1(k2_funct_1('#skF_6'))) | r2_hidden('#skF_5', k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_1155, c_1142])).
% 4.09/1.69  tff(c_1158, plain, (~r2_hidden('#skF_5', k1_relat_1(k2_funct_1('#skF_6')))), inference(splitLeft, [status(thm)], [c_1157])).
% 4.09/1.69  tff(c_1161, plain, (~r2_hidden('#skF_5', k2_relat_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_34, c_1158])).
% 4.09/1.69  tff(c_1164, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_1161])).
% 4.09/1.69  tff(c_1165, plain, (r2_hidden('#skF_5', k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6')))), inference(splitRight, [status(thm)], [c_1157])).
% 4.09/1.69  tff(c_30, plain, (![C_49, B_47, A_46]: (k1_funct_1(k5_relat_1(C_49, B_47), A_46)=k1_funct_1(B_47, k1_funct_1(C_49, A_46)) | ~r2_hidden(A_46, k1_relat_1(k5_relat_1(C_49, B_47))) | ~v1_funct_1(C_49) | ~v1_relat_1(C_49) | ~v1_funct_1(B_47) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.09/1.69  tff(c_1187, plain, (k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'), '#skF_5')=k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), '#skF_5')) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_1165, c_30])).
% 4.09/1.69  tff(c_1193, plain, (k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'), '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_1143, c_1155, c_738, c_1187])).
% 4.09/1.69  tff(c_1195, plain, $false, inference(negUnitSimplification, [status(thm)], [c_737, c_1193])).
% 4.09/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.09/1.69  
% 4.09/1.69  Inference rules
% 4.09/1.69  ----------------------
% 4.09/1.69  #Ref     : 0
% 4.09/1.69  #Sup     : 273
% 4.09/1.69  #Fact    : 0
% 4.09/1.69  #Define  : 0
% 4.09/1.69  #Split   : 7
% 4.09/1.69  #Chain   : 0
% 4.09/1.70  #Close   : 0
% 4.09/1.70  
% 4.09/1.70  Ordering : KBO
% 4.09/1.70  
% 4.09/1.70  Simplification rules
% 4.09/1.70  ----------------------
% 4.09/1.70  #Subsume      : 3
% 4.09/1.70  #Demod        : 72
% 4.09/1.70  #Tautology    : 40
% 4.09/1.70  #SimpNegUnit  : 1
% 4.09/1.70  #BackRed      : 1
% 4.09/1.70  
% 4.09/1.70  #Partial instantiations: 0
% 4.09/1.70  #Strategies tried      : 1
% 4.09/1.70  
% 4.09/1.70  Timing (in seconds)
% 4.09/1.70  ----------------------
% 4.09/1.70  Preprocessing        : 0.33
% 4.09/1.70  Parsing              : 0.17
% 4.09/1.70  CNF conversion       : 0.03
% 4.09/1.70  Main loop            : 0.59
% 4.09/1.70  Inferencing          : 0.22
% 4.09/1.70  Reduction            : 0.16
% 4.09/1.70  Demodulation         : 0.11
% 4.09/1.70  BG Simplification    : 0.04
% 4.09/1.70  Subsumption          : 0.13
% 4.09/1.70  Abstraction          : 0.04
% 4.09/1.70  MUC search           : 0.00
% 4.09/1.70  Cooper               : 0.00
% 4.09/1.70  Total                : 0.96
% 4.09/1.70  Index Insertion      : 0.00
% 4.09/1.70  Index Deletion       : 0.00
% 4.09/1.70  Index Matching       : 0.00
% 4.09/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
