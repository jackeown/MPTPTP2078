%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:46 EST 2020

% Result     : Theorem 3.67s
% Output     : CNFRefutation 3.67s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 664 expanded)
%              Number of leaves         :   24 ( 240 expanded)
%              Depth                    :   18
%              Number of atoms          :  256 (2531 expanded)
%              Number of equality atoms :   59 ( 874 expanded)
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

tff(f_96,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( ( v2_funct_1(B)
            & r2_hidden(A,k2_relat_1(B)) )
         => ( A = k1_funct_1(B,k1_funct_1(k2_funct_1(B),A))
            & A = k1_funct_1(k5_relat_1(k2_funct_1(B),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_funct_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( v2_funct_1(B)
          & r2_hidden(A,k1_relat_1(B)) )
       => ( A = k1_funct_1(k2_funct_1(B),k1_funct_1(B,A))
          & A = k1_funct_1(k5_relat_1(B,k2_funct_1(B)),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_funct_1)).

tff(f_48,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

tff(c_42,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_40,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_36,plain,(
    r2_hidden('#skF_5',k2_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_4,plain,(
    ! [A_1,C_37] :
      ( k1_funct_1(A_1,'#skF_4'(A_1,k2_relat_1(A_1),C_37)) = C_37
      | ~ r2_hidden(C_37,k2_relat_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_38,plain,(
    v2_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_6,plain,(
    ! [A_1,C_37] :
      ( r2_hidden('#skF_4'(A_1,k2_relat_1(A_1),C_37),k1_relat_1(A_1))
      | ~ r2_hidden(C_37,k2_relat_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_111,plain,(
    ! [B_63,A_64] :
      ( k1_funct_1(k2_funct_1(B_63),k1_funct_1(B_63,A_64)) = A_64
      | ~ r2_hidden(A_64,k1_relat_1(B_63))
      | ~ v2_funct_1(B_63)
      | ~ v1_funct_1(B_63)
      | ~ v1_relat_1(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_383,plain,(
    ! [A_105,C_106] :
      ( k1_funct_1(k2_funct_1(A_105),C_106) = '#skF_4'(A_105,k2_relat_1(A_105),C_106)
      | ~ r2_hidden('#skF_4'(A_105,k2_relat_1(A_105),C_106),k1_relat_1(A_105))
      | ~ v2_funct_1(A_105)
      | ~ v1_funct_1(A_105)
      | ~ v1_relat_1(A_105)
      | ~ r2_hidden(C_106,k2_relat_1(A_105))
      | ~ v1_funct_1(A_105)
      | ~ v1_relat_1(A_105) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_111])).

tff(c_394,plain,(
    ! [A_107,C_108] :
      ( k1_funct_1(k2_funct_1(A_107),C_108) = '#skF_4'(A_107,k2_relat_1(A_107),C_108)
      | ~ v2_funct_1(A_107)
      | ~ r2_hidden(C_108,k2_relat_1(A_107))
      | ~ v1_funct_1(A_107)
      | ~ v1_relat_1(A_107) ) ),
    inference(resolution,[status(thm)],[c_6,c_383])).

tff(c_427,plain,
    ( k1_funct_1(k2_funct_1('#skF_6'),'#skF_5') = '#skF_4'('#skF_6',k2_relat_1('#skF_6'),'#skF_5')
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_394])).

tff(c_441,plain,(
    k1_funct_1(k2_funct_1('#skF_6'),'#skF_5') = '#skF_4'('#skF_6',k2_relat_1('#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_427])).

tff(c_34,plain,
    ( k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6'),'#skF_5') != '#skF_5'
    | k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),'#skF_5')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_67,plain,(
    k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),'#skF_5')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_508,plain,(
    k1_funct_1('#skF_6','#skF_4'('#skF_6',k2_relat_1('#skF_6'),'#skF_5')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_441,c_67])).

tff(c_533,plain,
    ( ~ r2_hidden('#skF_5',k2_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_508])).

tff(c_537,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_36,c_533])).

tff(c_539,plain,(
    k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),'#skF_5')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_22,plain,(
    ! [A_41] :
      ( v1_relat_1(k2_funct_1(A_41))
      | ~ v1_funct_1(A_41)
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_20,plain,(
    ! [A_41] :
      ( v1_funct_1(k2_funct_1(A_41))
      | ~ v1_funct_1(A_41)
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_28,plain,(
    ! [A_46] :
      ( k1_relat_1(k2_funct_1(A_46)) = k2_relat_1(A_46)
      | ~ v2_funct_1(A_46)
      | ~ v1_funct_1(A_46)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_26,plain,(
    ! [A_46] :
      ( k2_relat_1(k2_funct_1(A_46)) = k1_relat_1(A_46)
      | ~ v2_funct_1(A_46)
      | ~ v1_funct_1(A_46)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_63,plain,(
    ! [A_53,D_54] :
      ( r2_hidden(k1_funct_1(A_53,D_54),k2_relat_1(A_53))
      | ~ r2_hidden(D_54,k1_relat_1(A_53))
      | ~ v1_funct_1(A_53)
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_685,plain,(
    ! [A_135,D_136] :
      ( r2_hidden(k1_funct_1(k2_funct_1(A_135),D_136),k1_relat_1(A_135))
      | ~ r2_hidden(D_136,k1_relat_1(k2_funct_1(A_135)))
      | ~ v1_funct_1(k2_funct_1(A_135))
      | ~ v1_relat_1(k2_funct_1(A_135))
      | ~ v2_funct_1(A_135)
      | ~ v1_funct_1(A_135)
      | ~ v1_relat_1(A_135) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_63])).

tff(c_671,plain,(
    ! [A_132,B_133,D_134] :
      ( r2_hidden('#skF_2'(A_132,B_133),k1_relat_1(A_132))
      | k1_funct_1(A_132,D_134) != '#skF_3'(A_132,B_133)
      | ~ r2_hidden(D_134,k1_relat_1(A_132))
      | k2_relat_1(A_132) = B_133
      | ~ v1_funct_1(A_132)
      | ~ v1_relat_1(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_681,plain,(
    ! [B_133] :
      ( r2_hidden('#skF_2'('#skF_6',B_133),k1_relat_1('#skF_6'))
      | '#skF_3'('#skF_6',B_133) != '#skF_5'
      | ~ r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),'#skF_5'),k1_relat_1('#skF_6'))
      | k2_relat_1('#skF_6') = B_133
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_539,c_671])).

tff(c_683,plain,(
    ! [B_133] :
      ( r2_hidden('#skF_2'('#skF_6',B_133),k1_relat_1('#skF_6'))
      | '#skF_3'('#skF_6',B_133) != '#skF_5'
      | ~ r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),'#skF_5'),k1_relat_1('#skF_6'))
      | k2_relat_1('#skF_6') = B_133 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_681])).

tff(c_684,plain,(
    ~ r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),'#skF_5'),k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_683])).

tff(c_688,plain,
    ( ~ r2_hidden('#skF_5',k1_relat_1(k2_funct_1('#skF_6')))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_685,c_684])).

tff(c_707,plain,
    ( ~ r2_hidden('#skF_5',k1_relat_1(k2_funct_1('#skF_6')))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_688])).

tff(c_709,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_707])).

tff(c_712,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_22,c_709])).

tff(c_716,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_712])).

tff(c_717,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ r2_hidden('#skF_5',k1_relat_1(k2_funct_1('#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_707])).

tff(c_732,plain,(
    ~ r2_hidden('#skF_5',k1_relat_1(k2_funct_1('#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_717])).

tff(c_735,plain,
    ( ~ r2_hidden('#skF_5',k2_relat_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_732])).

tff(c_738,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_735])).

tff(c_739,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_717])).

tff(c_743,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_20,c_739])).

tff(c_747,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_743])).

tff(c_748,plain,(
    ! [B_133] :
      ( r2_hidden('#skF_2'('#skF_6',B_133),k1_relat_1('#skF_6'))
      | '#skF_3'('#skF_6',B_133) != '#skF_5'
      | k2_relat_1('#skF_6') = B_133 ) ),
    inference(splitRight,[status(thm)],[c_683])).

tff(c_749,plain,(
    r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),'#skF_5'),k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_683])).

tff(c_810,plain,(
    ! [A_144,B_145,D_146] :
      ( k1_funct_1(A_144,'#skF_2'(A_144,B_145)) = '#skF_1'(A_144,B_145)
      | k1_funct_1(A_144,D_146) != '#skF_3'(A_144,B_145)
      | ~ r2_hidden(D_146,k1_relat_1(A_144))
      | k2_relat_1(A_144) = B_145
      | ~ v1_funct_1(A_144)
      | ~ v1_relat_1(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_822,plain,(
    ! [B_145] :
      ( k1_funct_1('#skF_6','#skF_2'('#skF_6',B_145)) = '#skF_1'('#skF_6',B_145)
      | '#skF_3'('#skF_6',B_145) != '#skF_5'
      | ~ r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),'#skF_5'),k1_relat_1('#skF_6'))
      | k2_relat_1('#skF_6') = B_145
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_539,c_810])).

tff(c_825,plain,(
    ! [B_147] :
      ( k1_funct_1('#skF_6','#skF_2'('#skF_6',B_147)) = '#skF_1'('#skF_6',B_147)
      | '#skF_3'('#skF_6',B_147) != '#skF_5'
      | k2_relat_1('#skF_6') = B_147 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_749,c_822])).

tff(c_32,plain,(
    ! [B_48,A_47] :
      ( k1_funct_1(k2_funct_1(B_48),k1_funct_1(B_48,A_47)) = A_47
      | ~ r2_hidden(A_47,k1_relat_1(B_48))
      | ~ v2_funct_1(B_48)
      | ~ v1_funct_1(B_48)
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_836,plain,(
    ! [B_147] :
      ( k1_funct_1(k2_funct_1('#skF_6'),'#skF_1'('#skF_6',B_147)) = '#skF_2'('#skF_6',B_147)
      | ~ r2_hidden('#skF_2'('#skF_6',B_147),k1_relat_1('#skF_6'))
      | ~ v2_funct_1('#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | '#skF_3'('#skF_6',B_147) != '#skF_5'
      | k2_relat_1('#skF_6') = B_147 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_825,c_32])).

tff(c_875,plain,(
    ! [B_150] :
      ( k1_funct_1(k2_funct_1('#skF_6'),'#skF_1'('#skF_6',B_150)) = '#skF_2'('#skF_6',B_150)
      | ~ r2_hidden('#skF_2'('#skF_6',B_150),k1_relat_1('#skF_6'))
      | '#skF_3'('#skF_6',B_150) != '#skF_5'
      | k2_relat_1('#skF_6') = B_150 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_836])).

tff(c_887,plain,(
    ! [B_151] :
      ( k1_funct_1(k2_funct_1('#skF_6'),'#skF_1'('#skF_6',B_151)) = '#skF_2'('#skF_6',B_151)
      | '#skF_3'('#skF_6',B_151) != '#skF_5'
      | k2_relat_1('#skF_6') = B_151 ) ),
    inference(resolution,[status(thm)],[c_748,c_875])).

tff(c_2,plain,(
    ! [A_1,D_40] :
      ( r2_hidden(k1_funct_1(A_1,D_40),k2_relat_1(A_1))
      | ~ r2_hidden(D_40,k1_relat_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_903,plain,(
    ! [B_151] :
      ( r2_hidden('#skF_2'('#skF_6',B_151),k2_relat_1(k2_funct_1('#skF_6')))
      | ~ r2_hidden('#skF_1'('#skF_6',B_151),k1_relat_1(k2_funct_1('#skF_6')))
      | ~ v1_funct_1(k2_funct_1('#skF_6'))
      | ~ v1_relat_1(k2_funct_1('#skF_6'))
      | '#skF_3'('#skF_6',B_151) != '#skF_5'
      | k2_relat_1('#skF_6') = B_151 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_887,c_2])).

tff(c_984,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_903])).

tff(c_987,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_22,c_984])).

tff(c_991,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_987])).

tff(c_993,plain,(
    v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_903])).

tff(c_992,plain,(
    ! [B_151] :
      ( ~ v1_funct_1(k2_funct_1('#skF_6'))
      | r2_hidden('#skF_2'('#skF_6',B_151),k2_relat_1(k2_funct_1('#skF_6')))
      | ~ r2_hidden('#skF_1'('#skF_6',B_151),k1_relat_1(k2_funct_1('#skF_6')))
      | '#skF_3'('#skF_6',B_151) != '#skF_5'
      | k2_relat_1('#skF_6') = B_151 ) ),
    inference(splitRight,[status(thm)],[c_903])).

tff(c_995,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_992])).

tff(c_998,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_20,c_995])).

tff(c_1002,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_998])).

tff(c_1004,plain,(
    v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_992])).

tff(c_592,plain,(
    ! [B_120,A_121] :
      ( k1_funct_1(k2_funct_1(B_120),k1_funct_1(B_120,A_121)) = A_121
      | ~ r2_hidden(A_121,k1_relat_1(B_120))
      | ~ v2_funct_1(B_120)
      | ~ v1_funct_1(B_120)
      | ~ v1_relat_1(B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1022,plain,(
    ! [A_165,B_166] :
      ( r2_hidden(A_165,k2_relat_1(k2_funct_1(B_166)))
      | ~ r2_hidden(k1_funct_1(B_166,A_165),k1_relat_1(k2_funct_1(B_166)))
      | ~ v1_funct_1(k2_funct_1(B_166))
      | ~ v1_relat_1(k2_funct_1(B_166))
      | ~ r2_hidden(A_165,k1_relat_1(B_166))
      | ~ v2_funct_1(B_166)
      | ~ v1_funct_1(B_166)
      | ~ v1_relat_1(B_166) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_592,c_2])).

tff(c_1052,plain,
    ( r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),'#skF_5'),k2_relat_1(k2_funct_1('#skF_6')))
    | ~ r2_hidden('#skF_5',k1_relat_1(k2_funct_1('#skF_6')))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),'#skF_5'),k1_relat_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_539,c_1022])).

tff(c_1061,plain,
    ( r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),'#skF_5'),k2_relat_1(k2_funct_1('#skF_6')))
    | ~ r2_hidden('#skF_5',k1_relat_1(k2_funct_1('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_749,c_993,c_1004,c_1052])).

tff(c_1062,plain,(
    ~ r2_hidden('#skF_5',k1_relat_1(k2_funct_1('#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_1061])).

tff(c_1065,plain,
    ( ~ r2_hidden('#skF_5',k2_relat_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1062])).

tff(c_1068,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_1065])).

tff(c_1070,plain,(
    r2_hidden('#skF_5',k1_relat_1(k2_funct_1('#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_1061])).

tff(c_24,plain,(
    ! [B_43,C_45,A_42] :
      ( k1_funct_1(k5_relat_1(B_43,C_45),A_42) = k1_funct_1(C_45,k1_funct_1(B_43,A_42))
      | ~ r2_hidden(A_42,k1_relat_1(B_43))
      | ~ v1_funct_1(C_45)
      | ~ v1_relat_1(C_45)
      | ~ v1_funct_1(B_43)
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1072,plain,(
    ! [C_45] :
      ( k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'),C_45),'#skF_5') = k1_funct_1(C_45,k1_funct_1(k2_funct_1('#skF_6'),'#skF_5'))
      | ~ v1_funct_1(C_45)
      | ~ v1_relat_1(C_45)
      | ~ v1_funct_1(k2_funct_1('#skF_6'))
      | ~ v1_relat_1(k2_funct_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_1070,c_24])).

tff(c_1086,plain,(
    ! [C_167] :
      ( k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'),C_167),'#skF_5') = k1_funct_1(C_167,k1_funct_1(k2_funct_1('#skF_6'),'#skF_5'))
      | ~ v1_funct_1(C_167)
      | ~ v1_relat_1(C_167) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_993,c_1004,c_1072])).

tff(c_538,plain,(
    k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6'),'#skF_5') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_1106,plain,
    ( k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),'#skF_5')) != '#skF_5'
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1086,c_538])).

tff(c_1122,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_539,c_1106])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:30:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.67/1.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.67/1.63  
% 3.67/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.67/1.64  %$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1
% 3.67/1.64  
% 3.67/1.64  %Foreground sorts:
% 3.67/1.64  
% 3.67/1.64  
% 3.67/1.64  %Background operators:
% 3.67/1.64  
% 3.67/1.64  
% 3.67/1.64  %Foreground operators:
% 3.67/1.64  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.67/1.64  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.67/1.64  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.67/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.67/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.67/1.64  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.67/1.64  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.67/1.64  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.67/1.64  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.67/1.64  tff('#skF_5', type, '#skF_5': $i).
% 3.67/1.64  tff('#skF_6', type, '#skF_6': $i).
% 3.67/1.64  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.67/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.67/1.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.67/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.67/1.64  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.67/1.64  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.67/1.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.67/1.64  
% 3.67/1.66  tff(f_96, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k2_relat_1(B))) => ((A = k1_funct_1(B, k1_funct_1(k2_funct_1(B), A))) & (A = k1_funct_1(k5_relat_1(k2_funct_1(B), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_funct_1)).
% 3.67/1.66  tff(f_40, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 3.67/1.66  tff(f_83, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k1_relat_1(B))) => ((A = k1_funct_1(k2_funct_1(B), k1_funct_1(B, A))) & (A = k1_funct_1(k5_relat_1(B, k2_funct_1(B)), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_funct_1)).
% 3.67/1.66  tff(f_48, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 3.67/1.66  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 3.67/1.66  tff(f_61, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_1)).
% 3.67/1.66  tff(c_42, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.67/1.66  tff(c_40, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.67/1.66  tff(c_36, plain, (r2_hidden('#skF_5', k2_relat_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.67/1.66  tff(c_4, plain, (![A_1, C_37]: (k1_funct_1(A_1, '#skF_4'(A_1, k2_relat_1(A_1), C_37))=C_37 | ~r2_hidden(C_37, k2_relat_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.67/1.66  tff(c_38, plain, (v2_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.67/1.66  tff(c_6, plain, (![A_1, C_37]: (r2_hidden('#skF_4'(A_1, k2_relat_1(A_1), C_37), k1_relat_1(A_1)) | ~r2_hidden(C_37, k2_relat_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.67/1.66  tff(c_111, plain, (![B_63, A_64]: (k1_funct_1(k2_funct_1(B_63), k1_funct_1(B_63, A_64))=A_64 | ~r2_hidden(A_64, k1_relat_1(B_63)) | ~v2_funct_1(B_63) | ~v1_funct_1(B_63) | ~v1_relat_1(B_63))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.67/1.66  tff(c_383, plain, (![A_105, C_106]: (k1_funct_1(k2_funct_1(A_105), C_106)='#skF_4'(A_105, k2_relat_1(A_105), C_106) | ~r2_hidden('#skF_4'(A_105, k2_relat_1(A_105), C_106), k1_relat_1(A_105)) | ~v2_funct_1(A_105) | ~v1_funct_1(A_105) | ~v1_relat_1(A_105) | ~r2_hidden(C_106, k2_relat_1(A_105)) | ~v1_funct_1(A_105) | ~v1_relat_1(A_105))), inference(superposition, [status(thm), theory('equality')], [c_4, c_111])).
% 3.67/1.66  tff(c_394, plain, (![A_107, C_108]: (k1_funct_1(k2_funct_1(A_107), C_108)='#skF_4'(A_107, k2_relat_1(A_107), C_108) | ~v2_funct_1(A_107) | ~r2_hidden(C_108, k2_relat_1(A_107)) | ~v1_funct_1(A_107) | ~v1_relat_1(A_107))), inference(resolution, [status(thm)], [c_6, c_383])).
% 3.67/1.66  tff(c_427, plain, (k1_funct_1(k2_funct_1('#skF_6'), '#skF_5')='#skF_4'('#skF_6', k2_relat_1('#skF_6'), '#skF_5') | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_36, c_394])).
% 3.67/1.66  tff(c_441, plain, (k1_funct_1(k2_funct_1('#skF_6'), '#skF_5')='#skF_4'('#skF_6', k2_relat_1('#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_427])).
% 3.67/1.66  tff(c_34, plain, (k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'), '#skF_5')!='#skF_5' | k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.67/1.66  tff(c_67, plain, (k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_34])).
% 3.67/1.66  tff(c_508, plain, (k1_funct_1('#skF_6', '#skF_4'('#skF_6', k2_relat_1('#skF_6'), '#skF_5'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_441, c_67])).
% 3.67/1.66  tff(c_533, plain, (~r2_hidden('#skF_5', k2_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_4, c_508])).
% 3.67/1.66  tff(c_537, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_36, c_533])).
% 3.67/1.66  tff(c_539, plain, (k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'))='#skF_5'), inference(splitRight, [status(thm)], [c_34])).
% 3.67/1.66  tff(c_22, plain, (![A_41]: (v1_relat_1(k2_funct_1(A_41)) | ~v1_funct_1(A_41) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.67/1.66  tff(c_20, plain, (![A_41]: (v1_funct_1(k2_funct_1(A_41)) | ~v1_funct_1(A_41) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.67/1.66  tff(c_28, plain, (![A_46]: (k1_relat_1(k2_funct_1(A_46))=k2_relat_1(A_46) | ~v2_funct_1(A_46) | ~v1_funct_1(A_46) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.67/1.66  tff(c_26, plain, (![A_46]: (k2_relat_1(k2_funct_1(A_46))=k1_relat_1(A_46) | ~v2_funct_1(A_46) | ~v1_funct_1(A_46) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.67/1.66  tff(c_63, plain, (![A_53, D_54]: (r2_hidden(k1_funct_1(A_53, D_54), k2_relat_1(A_53)) | ~r2_hidden(D_54, k1_relat_1(A_53)) | ~v1_funct_1(A_53) | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.67/1.66  tff(c_685, plain, (![A_135, D_136]: (r2_hidden(k1_funct_1(k2_funct_1(A_135), D_136), k1_relat_1(A_135)) | ~r2_hidden(D_136, k1_relat_1(k2_funct_1(A_135))) | ~v1_funct_1(k2_funct_1(A_135)) | ~v1_relat_1(k2_funct_1(A_135)) | ~v2_funct_1(A_135) | ~v1_funct_1(A_135) | ~v1_relat_1(A_135))), inference(superposition, [status(thm), theory('equality')], [c_26, c_63])).
% 3.67/1.66  tff(c_671, plain, (![A_132, B_133, D_134]: (r2_hidden('#skF_2'(A_132, B_133), k1_relat_1(A_132)) | k1_funct_1(A_132, D_134)!='#skF_3'(A_132, B_133) | ~r2_hidden(D_134, k1_relat_1(A_132)) | k2_relat_1(A_132)=B_133 | ~v1_funct_1(A_132) | ~v1_relat_1(A_132))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.67/1.66  tff(c_681, plain, (![B_133]: (r2_hidden('#skF_2'('#skF_6', B_133), k1_relat_1('#skF_6')) | '#skF_3'('#skF_6', B_133)!='#skF_5' | ~r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'), k1_relat_1('#skF_6')) | k2_relat_1('#skF_6')=B_133 | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_539, c_671])).
% 3.67/1.66  tff(c_683, plain, (![B_133]: (r2_hidden('#skF_2'('#skF_6', B_133), k1_relat_1('#skF_6')) | '#skF_3'('#skF_6', B_133)!='#skF_5' | ~r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'), k1_relat_1('#skF_6')) | k2_relat_1('#skF_6')=B_133)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_681])).
% 3.67/1.66  tff(c_684, plain, (~r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'), k1_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_683])).
% 3.67/1.66  tff(c_688, plain, (~r2_hidden('#skF_5', k1_relat_1(k2_funct_1('#skF_6'))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_685, c_684])).
% 3.67/1.66  tff(c_707, plain, (~r2_hidden('#skF_5', k1_relat_1(k2_funct_1('#skF_6'))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_688])).
% 3.67/1.66  tff(c_709, plain, (~v1_relat_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_707])).
% 3.67/1.66  tff(c_712, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_22, c_709])).
% 3.67/1.66  tff(c_716, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_712])).
% 3.67/1.66  tff(c_717, plain, (~v1_funct_1(k2_funct_1('#skF_6')) | ~r2_hidden('#skF_5', k1_relat_1(k2_funct_1('#skF_6')))), inference(splitRight, [status(thm)], [c_707])).
% 3.67/1.66  tff(c_732, plain, (~r2_hidden('#skF_5', k1_relat_1(k2_funct_1('#skF_6')))), inference(splitLeft, [status(thm)], [c_717])).
% 3.67/1.66  tff(c_735, plain, (~r2_hidden('#skF_5', k2_relat_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_28, c_732])).
% 3.67/1.66  tff(c_738, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_735])).
% 3.67/1.66  tff(c_739, plain, (~v1_funct_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_717])).
% 3.67/1.66  tff(c_743, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_20, c_739])).
% 3.67/1.66  tff(c_747, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_743])).
% 3.67/1.66  tff(c_748, plain, (![B_133]: (r2_hidden('#skF_2'('#skF_6', B_133), k1_relat_1('#skF_6')) | '#skF_3'('#skF_6', B_133)!='#skF_5' | k2_relat_1('#skF_6')=B_133)), inference(splitRight, [status(thm)], [c_683])).
% 3.67/1.66  tff(c_749, plain, (r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'), k1_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_683])).
% 3.67/1.66  tff(c_810, plain, (![A_144, B_145, D_146]: (k1_funct_1(A_144, '#skF_2'(A_144, B_145))='#skF_1'(A_144, B_145) | k1_funct_1(A_144, D_146)!='#skF_3'(A_144, B_145) | ~r2_hidden(D_146, k1_relat_1(A_144)) | k2_relat_1(A_144)=B_145 | ~v1_funct_1(A_144) | ~v1_relat_1(A_144))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.67/1.66  tff(c_822, plain, (![B_145]: (k1_funct_1('#skF_6', '#skF_2'('#skF_6', B_145))='#skF_1'('#skF_6', B_145) | '#skF_3'('#skF_6', B_145)!='#skF_5' | ~r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'), k1_relat_1('#skF_6')) | k2_relat_1('#skF_6')=B_145 | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_539, c_810])).
% 3.67/1.66  tff(c_825, plain, (![B_147]: (k1_funct_1('#skF_6', '#skF_2'('#skF_6', B_147))='#skF_1'('#skF_6', B_147) | '#skF_3'('#skF_6', B_147)!='#skF_5' | k2_relat_1('#skF_6')=B_147)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_749, c_822])).
% 3.67/1.66  tff(c_32, plain, (![B_48, A_47]: (k1_funct_1(k2_funct_1(B_48), k1_funct_1(B_48, A_47))=A_47 | ~r2_hidden(A_47, k1_relat_1(B_48)) | ~v2_funct_1(B_48) | ~v1_funct_1(B_48) | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.67/1.66  tff(c_836, plain, (![B_147]: (k1_funct_1(k2_funct_1('#skF_6'), '#skF_1'('#skF_6', B_147))='#skF_2'('#skF_6', B_147) | ~r2_hidden('#skF_2'('#skF_6', B_147), k1_relat_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_3'('#skF_6', B_147)!='#skF_5' | k2_relat_1('#skF_6')=B_147)), inference(superposition, [status(thm), theory('equality')], [c_825, c_32])).
% 3.67/1.66  tff(c_875, plain, (![B_150]: (k1_funct_1(k2_funct_1('#skF_6'), '#skF_1'('#skF_6', B_150))='#skF_2'('#skF_6', B_150) | ~r2_hidden('#skF_2'('#skF_6', B_150), k1_relat_1('#skF_6')) | '#skF_3'('#skF_6', B_150)!='#skF_5' | k2_relat_1('#skF_6')=B_150)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_836])).
% 3.67/1.66  tff(c_887, plain, (![B_151]: (k1_funct_1(k2_funct_1('#skF_6'), '#skF_1'('#skF_6', B_151))='#skF_2'('#skF_6', B_151) | '#skF_3'('#skF_6', B_151)!='#skF_5' | k2_relat_1('#skF_6')=B_151)), inference(resolution, [status(thm)], [c_748, c_875])).
% 3.67/1.66  tff(c_2, plain, (![A_1, D_40]: (r2_hidden(k1_funct_1(A_1, D_40), k2_relat_1(A_1)) | ~r2_hidden(D_40, k1_relat_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.67/1.66  tff(c_903, plain, (![B_151]: (r2_hidden('#skF_2'('#skF_6', B_151), k2_relat_1(k2_funct_1('#skF_6'))) | ~r2_hidden('#skF_1'('#skF_6', B_151), k1_relat_1(k2_funct_1('#skF_6'))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | '#skF_3'('#skF_6', B_151)!='#skF_5' | k2_relat_1('#skF_6')=B_151)), inference(superposition, [status(thm), theory('equality')], [c_887, c_2])).
% 3.67/1.66  tff(c_984, plain, (~v1_relat_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_903])).
% 3.67/1.66  tff(c_987, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_22, c_984])).
% 3.67/1.66  tff(c_991, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_987])).
% 3.67/1.66  tff(c_993, plain, (v1_relat_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_903])).
% 3.67/1.66  tff(c_992, plain, (![B_151]: (~v1_funct_1(k2_funct_1('#skF_6')) | r2_hidden('#skF_2'('#skF_6', B_151), k2_relat_1(k2_funct_1('#skF_6'))) | ~r2_hidden('#skF_1'('#skF_6', B_151), k1_relat_1(k2_funct_1('#skF_6'))) | '#skF_3'('#skF_6', B_151)!='#skF_5' | k2_relat_1('#skF_6')=B_151)), inference(splitRight, [status(thm)], [c_903])).
% 3.67/1.66  tff(c_995, plain, (~v1_funct_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_992])).
% 3.67/1.66  tff(c_998, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_20, c_995])).
% 3.67/1.66  tff(c_1002, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_998])).
% 3.67/1.66  tff(c_1004, plain, (v1_funct_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_992])).
% 3.67/1.66  tff(c_592, plain, (![B_120, A_121]: (k1_funct_1(k2_funct_1(B_120), k1_funct_1(B_120, A_121))=A_121 | ~r2_hidden(A_121, k1_relat_1(B_120)) | ~v2_funct_1(B_120) | ~v1_funct_1(B_120) | ~v1_relat_1(B_120))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.67/1.66  tff(c_1022, plain, (![A_165, B_166]: (r2_hidden(A_165, k2_relat_1(k2_funct_1(B_166))) | ~r2_hidden(k1_funct_1(B_166, A_165), k1_relat_1(k2_funct_1(B_166))) | ~v1_funct_1(k2_funct_1(B_166)) | ~v1_relat_1(k2_funct_1(B_166)) | ~r2_hidden(A_165, k1_relat_1(B_166)) | ~v2_funct_1(B_166) | ~v1_funct_1(B_166) | ~v1_relat_1(B_166))), inference(superposition, [status(thm), theory('equality')], [c_592, c_2])).
% 3.67/1.66  tff(c_1052, plain, (r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'), k2_relat_1(k2_funct_1('#skF_6'))) | ~r2_hidden('#skF_5', k1_relat_1(k2_funct_1('#skF_6'))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'), k1_relat_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_539, c_1022])).
% 3.67/1.66  tff(c_1061, plain, (r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'), k2_relat_1(k2_funct_1('#skF_6'))) | ~r2_hidden('#skF_5', k1_relat_1(k2_funct_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_749, c_993, c_1004, c_1052])).
% 3.67/1.66  tff(c_1062, plain, (~r2_hidden('#skF_5', k1_relat_1(k2_funct_1('#skF_6')))), inference(splitLeft, [status(thm)], [c_1061])).
% 3.67/1.66  tff(c_1065, plain, (~r2_hidden('#skF_5', k2_relat_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_28, c_1062])).
% 3.67/1.66  tff(c_1068, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_1065])).
% 3.67/1.66  tff(c_1070, plain, (r2_hidden('#skF_5', k1_relat_1(k2_funct_1('#skF_6')))), inference(splitRight, [status(thm)], [c_1061])).
% 3.67/1.66  tff(c_24, plain, (![B_43, C_45, A_42]: (k1_funct_1(k5_relat_1(B_43, C_45), A_42)=k1_funct_1(C_45, k1_funct_1(B_43, A_42)) | ~r2_hidden(A_42, k1_relat_1(B_43)) | ~v1_funct_1(C_45) | ~v1_relat_1(C_45) | ~v1_funct_1(B_43) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.67/1.66  tff(c_1072, plain, (![C_45]: (k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'), C_45), '#skF_5')=k1_funct_1(C_45, k1_funct_1(k2_funct_1('#skF_6'), '#skF_5')) | ~v1_funct_1(C_45) | ~v1_relat_1(C_45) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')))), inference(resolution, [status(thm)], [c_1070, c_24])).
% 3.67/1.66  tff(c_1086, plain, (![C_167]: (k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'), C_167), '#skF_5')=k1_funct_1(C_167, k1_funct_1(k2_funct_1('#skF_6'), '#skF_5')) | ~v1_funct_1(C_167) | ~v1_relat_1(C_167))), inference(demodulation, [status(thm), theory('equality')], [c_993, c_1004, c_1072])).
% 3.67/1.66  tff(c_538, plain, (k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'), '#skF_5')!='#skF_5'), inference(splitRight, [status(thm)], [c_34])).
% 3.67/1.66  tff(c_1106, plain, (k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'))!='#skF_5' | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1086, c_538])).
% 3.67/1.66  tff(c_1122, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_539, c_1106])).
% 3.67/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.67/1.66  
% 3.67/1.66  Inference rules
% 3.67/1.66  ----------------------
% 3.67/1.66  #Ref     : 0
% 3.67/1.66  #Sup     : 283
% 3.67/1.66  #Fact    : 0
% 3.67/1.66  #Define  : 0
% 3.67/1.66  #Split   : 7
% 3.67/1.66  #Chain   : 0
% 3.67/1.66  #Close   : 0
% 3.67/1.66  
% 3.67/1.66  Ordering : KBO
% 3.67/1.66  
% 3.67/1.66  Simplification rules
% 3.67/1.66  ----------------------
% 3.67/1.66  #Subsume      : 17
% 3.67/1.66  #Demod        : 113
% 3.67/1.66  #Tautology    : 61
% 3.67/1.66  #SimpNegUnit  : 0
% 3.67/1.66  #BackRed      : 1
% 3.67/1.66  
% 3.67/1.66  #Partial instantiations: 0
% 3.67/1.66  #Strategies tried      : 1
% 3.67/1.66  
% 3.67/1.66  Timing (in seconds)
% 3.67/1.66  ----------------------
% 4.00/1.67  Preprocessing        : 0.31
% 4.00/1.67  Parsing              : 0.16
% 4.00/1.67  CNF conversion       : 0.03
% 4.00/1.67  Main loop            : 0.57
% 4.00/1.67  Inferencing          : 0.22
% 4.00/1.67  Reduction            : 0.15
% 4.00/1.67  Demodulation         : 0.11
% 4.00/1.67  BG Simplification    : 0.04
% 4.00/1.67  Subsumption          : 0.13
% 4.00/1.67  Abstraction          : 0.04
% 4.00/1.67  MUC search           : 0.00
% 4.00/1.67  Cooper               : 0.00
% 4.00/1.67  Total                : 0.93
% 4.00/1.67  Index Insertion      : 0.00
% 4.00/1.67  Index Deletion       : 0.00
% 4.00/1.67  Index Matching       : 0.00
% 4.00/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
