%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:47 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 338 expanded)
%              Number of leaves         :   23 ( 129 expanded)
%              Depth                    :   12
%              Number of atoms          :  207 (1323 expanded)
%              Number of equality atoms :   21 ( 233 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_106,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( ( v2_funct_1(B)
            & r2_hidden(A,k2_relat_1(B)) )
         => ( A = k1_funct_1(B,k1_funct_1(k2_funct_1(B),A))
            & A = k1_funct_1(k5_relat_1(k2_funct_1(B),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_funct_1)).

tff(f_33,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_93,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( B = k2_funct_1(A)
            <=> ( k1_relat_1(B) = k2_relat_1(A)
                & ! [C,D] :
                    ( ( ( r2_hidden(C,k2_relat_1(A))
                        & D = k1_funct_1(B,C) )
                     => ( r2_hidden(D,k1_relat_1(A))
                        & C = k1_funct_1(A,D) ) )
                    & ( ( r2_hidden(D,k1_relat_1(A))
                        & C = k1_funct_1(A,D) )
                     => ( r2_hidden(C,k2_relat_1(A))
                        & D = k1_funct_1(B,C) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_funct_1)).

tff(f_48,axiom,(
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

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
           => k1_funct_1(k5_relat_1(C,B),A) = k1_funct_1(B,k1_funct_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_1)).

tff(c_50,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_48,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_funct_1(k2_funct_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_relat_1(k2_funct_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_46,plain,(
    v2_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_44,plain,(
    r2_hidden('#skF_5',k2_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_84,plain,(
    ! [A_40,C_41] :
      ( k1_funct_1(A_40,k1_funct_1(k2_funct_1(A_40),C_41)) = C_41
      | ~ r2_hidden(C_41,k2_relat_1(A_40))
      | ~ v1_funct_1(k2_funct_1(A_40))
      | ~ v1_relat_1(k2_funct_1(A_40))
      | ~ v2_funct_1(A_40)
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_42,plain,
    ( k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6'),'#skF_5') != '#skF_5'
    | k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),'#skF_5')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_53,plain,(
    k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),'#skF_5')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_100,plain,
    ( ~ r2_hidden('#skF_5',k2_relat_1('#skF_6'))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_53])).

tff(c_111,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_100])).

tff(c_142,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_111])).

tff(c_145,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_142])).

tff(c_149,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_145])).

tff(c_150,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_111])).

tff(c_154,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2,c_150])).

tff(c_158,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_154])).

tff(c_159,plain,(
    k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6'),'#skF_5') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_8,plain,(
    ! [C_5,A_2,B_3] :
      ( r2_hidden(k1_funct_1(C_5,A_2),k1_relat_1(B_3))
      | ~ r2_hidden(A_2,k1_relat_1(k5_relat_1(C_5,B_3)))
      | ~ v1_funct_1(C_5)
      | ~ v1_relat_1(C_5)
      | ~ v1_funct_1(B_3)
      | ~ v1_relat_1(B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_160,plain,(
    k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),'#skF_5')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_185,plain,(
    ! [C_50,A_51,B_52] :
      ( r2_hidden(k1_funct_1(C_50,A_51),k1_relat_1(B_52))
      | ~ r2_hidden(A_51,k1_relat_1(k5_relat_1(C_50,B_52)))
      | ~ v1_funct_1(C_50)
      | ~ v1_relat_1(C_50)
      | ~ v1_funct_1(B_52)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_195,plain,(
    ! [B_52] :
      ( r2_hidden('#skF_5',k1_relat_1(B_52))
      | ~ r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),'#skF_5'),k1_relat_1(k5_relat_1('#skF_6',B_52)))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | ~ v1_funct_1(B_52)
      | ~ v1_relat_1(B_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_185])).

tff(c_199,plain,(
    ! [B_53] :
      ( r2_hidden('#skF_5',k1_relat_1(B_53))
      | ~ r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),'#skF_5'),k1_relat_1(k5_relat_1('#skF_6',B_53)))
      | ~ v1_funct_1(B_53)
      | ~ v1_relat_1(B_53) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_195])).

tff(c_203,plain,(
    ! [B_53] :
      ( r2_hidden('#skF_5',k1_relat_1(B_53))
      | ~ v1_funct_1(B_53)
      | ~ v1_relat_1(B_53)
      | ~ r2_hidden('#skF_5',k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'),k5_relat_1('#skF_6',B_53))))
      | ~ v1_funct_1(k2_funct_1('#skF_6'))
      | ~ v1_relat_1(k2_funct_1('#skF_6'))
      | ~ v1_funct_1(k5_relat_1('#skF_6',B_53))
      | ~ v1_relat_1(k5_relat_1('#skF_6',B_53)) ) ),
    inference(resolution,[status(thm)],[c_8,c_199])).

tff(c_210,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_203])).

tff(c_213,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_210])).

tff(c_217,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_213])).

tff(c_219,plain,(
    v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_203])).

tff(c_36,plain,(
    ! [A_10,C_25] :
      ( r2_hidden(k1_funct_1(k2_funct_1(A_10),C_25),k1_relat_1(A_10))
      | ~ r2_hidden(C_25,k2_relat_1(A_10))
      | ~ v1_funct_1(k2_funct_1(A_10))
      | ~ v1_relat_1(k2_funct_1(A_10))
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_306,plain,(
    ! [A_62,C_63,B_64] :
      ( r2_hidden(A_62,k1_relat_1(k5_relat_1(C_63,B_64)))
      | ~ r2_hidden(k1_funct_1(C_63,A_62),k1_relat_1(B_64))
      | ~ r2_hidden(A_62,k1_relat_1(C_63))
      | ~ v1_funct_1(C_63)
      | ~ v1_relat_1(C_63)
      | ~ v1_funct_1(B_64)
      | ~ v1_relat_1(B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_324,plain,(
    ! [B_64] :
      ( r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),'#skF_5'),k1_relat_1(k5_relat_1('#skF_6',B_64)))
      | ~ r2_hidden('#skF_5',k1_relat_1(B_64))
      | ~ r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),'#skF_5'),k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | ~ v1_funct_1(B_64)
      | ~ v1_relat_1(B_64) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_306])).

tff(c_328,plain,(
    ! [B_64] :
      ( r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),'#skF_5'),k1_relat_1(k5_relat_1('#skF_6',B_64)))
      | ~ r2_hidden('#skF_5',k1_relat_1(B_64))
      | ~ r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),'#skF_5'),k1_relat_1('#skF_6'))
      | ~ v1_funct_1(B_64)
      | ~ v1_relat_1(B_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_324])).

tff(c_340,plain,(
    ~ r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),'#skF_5'),k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_328])).

tff(c_343,plain,
    ( ~ r2_hidden('#skF_5',k2_relat_1('#skF_6'))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_340])).

tff(c_349,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_219,c_44,c_343])).

tff(c_356,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2,c_349])).

tff(c_360,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_356])).

tff(c_362,plain,(
    r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),'#skF_5'),k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_328])).

tff(c_6,plain,(
    ! [A_2,C_5,B_3] :
      ( r2_hidden(A_2,k1_relat_1(k5_relat_1(C_5,B_3)))
      | ~ r2_hidden(k1_funct_1(C_5,A_2),k1_relat_1(B_3))
      | ~ r2_hidden(A_2,k1_relat_1(C_5))
      | ~ v1_funct_1(C_5)
      | ~ v1_relat_1(C_5)
      | ~ v1_funct_1(B_3)
      | ~ v1_relat_1(B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_365,plain,
    ( r2_hidden('#skF_5',k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6')))
    | ~ r2_hidden('#skF_5',k1_relat_1(k2_funct_1('#skF_6')))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_362,c_6])).

tff(c_368,plain,
    ( r2_hidden('#skF_5',k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6')))
    | ~ r2_hidden('#skF_5',k1_relat_1(k2_funct_1('#skF_6')))
    | ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_219,c_365])).

tff(c_369,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_368])).

tff(c_372,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2,c_369])).

tff(c_376,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_372])).

tff(c_378,plain,(
    v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_368])).

tff(c_165,plain,(
    ! [A_44] :
      ( k1_relat_1(k2_funct_1(A_44)) = k2_relat_1(A_44)
      | ~ v1_funct_1(k2_funct_1(A_44))
      | ~ v1_relat_1(k2_funct_1(A_44))
      | ~ v2_funct_1(A_44)
      | ~ v1_funct_1(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_170,plain,(
    ! [A_45] :
      ( k1_relat_1(k2_funct_1(A_45)) = k2_relat_1(A_45)
      | ~ v1_funct_1(k2_funct_1(A_45))
      | ~ v2_funct_1(A_45)
      | ~ v1_funct_1(A_45)
      | ~ v1_relat_1(A_45) ) ),
    inference(resolution,[status(thm)],[c_4,c_165])).

tff(c_174,plain,(
    ! [A_1] :
      ( k1_relat_1(k2_funct_1(A_1)) = k2_relat_1(A_1)
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_170])).

tff(c_377,plain,
    ( ~ r2_hidden('#skF_5',k1_relat_1(k2_funct_1('#skF_6')))
    | r2_hidden('#skF_5',k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_368])).

tff(c_380,plain,(
    ~ r2_hidden('#skF_5',k1_relat_1(k2_funct_1('#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_377])).

tff(c_383,plain,
    ( ~ r2_hidden('#skF_5',k2_relat_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_380])).

tff(c_386,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_383])).

tff(c_387,plain,(
    r2_hidden('#skF_5',k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_377])).

tff(c_12,plain,(
    ! [C_9,B_7,A_6] :
      ( k1_funct_1(k5_relat_1(C_9,B_7),A_6) = k1_funct_1(B_7,k1_funct_1(C_9,A_6))
      | ~ r2_hidden(A_6,k1_relat_1(k5_relat_1(C_9,B_7)))
      | ~ v1_funct_1(C_9)
      | ~ v1_relat_1(C_9)
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_419,plain,
    ( k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6'),'#skF_5') = k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),'#skF_5'))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_387,c_12])).

tff(c_425,plain,(
    k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6'),'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_219,c_378,c_160,c_419])).

tff(c_427,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_159,c_425])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:23:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.66/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.42  
% 2.97/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.42  %$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4
% 2.97/1.42  
% 2.97/1.42  %Foreground sorts:
% 2.97/1.42  
% 2.97/1.42  
% 2.97/1.42  %Background operators:
% 2.97/1.42  
% 2.97/1.42  
% 2.97/1.42  %Foreground operators:
% 2.97/1.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.97/1.42  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.97/1.42  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.97/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.97/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.97/1.42  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.97/1.42  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.97/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.97/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.97/1.42  tff('#skF_6', type, '#skF_6': $i).
% 2.97/1.42  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.97/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.97/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.97/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.97/1.42  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.97/1.42  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.97/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.97/1.42  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.97/1.42  
% 2.97/1.44  tff(f_106, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k2_relat_1(B))) => ((A = k1_funct_1(B, k1_funct_1(k2_funct_1(B), A))) & (A = k1_funct_1(k5_relat_1(k2_funct_1(B), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_funct_1)).
% 2.97/1.44  tff(f_33, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 2.97/1.44  tff(f_93, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k2_funct_1(A)) <=> ((k1_relat_1(B) = k2_relat_1(A)) & (![C, D]: (((r2_hidden(C, k2_relat_1(A)) & (D = k1_funct_1(B, C))) => (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))) & ((r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D))) => (r2_hidden(C, k2_relat_1(A)) & (D = k1_funct_1(B, C))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_funct_1)).
% 2.97/1.44  tff(f_48, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) <=> (r2_hidden(A, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, A), k1_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_funct_1)).
% 2.97/1.44  tff(f_61, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) => (k1_funct_1(k5_relat_1(C, B), A) = k1_funct_1(B, k1_funct_1(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_funct_1)).
% 2.97/1.44  tff(c_50, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.97/1.44  tff(c_48, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.97/1.44  tff(c_2, plain, (![A_1]: (v1_funct_1(k2_funct_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.97/1.44  tff(c_4, plain, (![A_1]: (v1_relat_1(k2_funct_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.97/1.44  tff(c_46, plain, (v2_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.97/1.44  tff(c_44, plain, (r2_hidden('#skF_5', k2_relat_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.97/1.44  tff(c_84, plain, (![A_40, C_41]: (k1_funct_1(A_40, k1_funct_1(k2_funct_1(A_40), C_41))=C_41 | ~r2_hidden(C_41, k2_relat_1(A_40)) | ~v1_funct_1(k2_funct_1(A_40)) | ~v1_relat_1(k2_funct_1(A_40)) | ~v2_funct_1(A_40) | ~v1_funct_1(A_40) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.97/1.44  tff(c_42, plain, (k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'), '#skF_5')!='#skF_5' | k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.97/1.44  tff(c_53, plain, (k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_42])).
% 2.97/1.44  tff(c_100, plain, (~r2_hidden('#skF_5', k2_relat_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_84, c_53])).
% 2.97/1.44  tff(c_111, plain, (~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_100])).
% 2.97/1.44  tff(c_142, plain, (~v1_relat_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_111])).
% 2.97/1.44  tff(c_145, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_4, c_142])).
% 2.97/1.44  tff(c_149, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_145])).
% 2.97/1.44  tff(c_150, plain, (~v1_funct_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_111])).
% 2.97/1.44  tff(c_154, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2, c_150])).
% 2.97/1.44  tff(c_158, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_154])).
% 2.97/1.44  tff(c_159, plain, (k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'), '#skF_5')!='#skF_5'), inference(splitRight, [status(thm)], [c_42])).
% 2.97/1.44  tff(c_8, plain, (![C_5, A_2, B_3]: (r2_hidden(k1_funct_1(C_5, A_2), k1_relat_1(B_3)) | ~r2_hidden(A_2, k1_relat_1(k5_relat_1(C_5, B_3))) | ~v1_funct_1(C_5) | ~v1_relat_1(C_5) | ~v1_funct_1(B_3) | ~v1_relat_1(B_3))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.97/1.44  tff(c_160, plain, (k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'))='#skF_5'), inference(splitRight, [status(thm)], [c_42])).
% 2.97/1.44  tff(c_185, plain, (![C_50, A_51, B_52]: (r2_hidden(k1_funct_1(C_50, A_51), k1_relat_1(B_52)) | ~r2_hidden(A_51, k1_relat_1(k5_relat_1(C_50, B_52))) | ~v1_funct_1(C_50) | ~v1_relat_1(C_50) | ~v1_funct_1(B_52) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.97/1.44  tff(c_195, plain, (![B_52]: (r2_hidden('#skF_5', k1_relat_1(B_52)) | ~r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'), k1_relat_1(k5_relat_1('#skF_6', B_52))) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_funct_1(B_52) | ~v1_relat_1(B_52))), inference(superposition, [status(thm), theory('equality')], [c_160, c_185])).
% 2.97/1.44  tff(c_199, plain, (![B_53]: (r2_hidden('#skF_5', k1_relat_1(B_53)) | ~r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'), k1_relat_1(k5_relat_1('#skF_6', B_53))) | ~v1_funct_1(B_53) | ~v1_relat_1(B_53))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_195])).
% 2.97/1.44  tff(c_203, plain, (![B_53]: (r2_hidden('#skF_5', k1_relat_1(B_53)) | ~v1_funct_1(B_53) | ~v1_relat_1(B_53) | ~r2_hidden('#skF_5', k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'), k5_relat_1('#skF_6', B_53)))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v1_funct_1(k5_relat_1('#skF_6', B_53)) | ~v1_relat_1(k5_relat_1('#skF_6', B_53)))), inference(resolution, [status(thm)], [c_8, c_199])).
% 2.97/1.44  tff(c_210, plain, (~v1_relat_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_203])).
% 2.97/1.44  tff(c_213, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_4, c_210])).
% 2.97/1.44  tff(c_217, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_213])).
% 2.97/1.44  tff(c_219, plain, (v1_relat_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_203])).
% 2.97/1.44  tff(c_36, plain, (![A_10, C_25]: (r2_hidden(k1_funct_1(k2_funct_1(A_10), C_25), k1_relat_1(A_10)) | ~r2_hidden(C_25, k2_relat_1(A_10)) | ~v1_funct_1(k2_funct_1(A_10)) | ~v1_relat_1(k2_funct_1(A_10)) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.97/1.44  tff(c_306, plain, (![A_62, C_63, B_64]: (r2_hidden(A_62, k1_relat_1(k5_relat_1(C_63, B_64))) | ~r2_hidden(k1_funct_1(C_63, A_62), k1_relat_1(B_64)) | ~r2_hidden(A_62, k1_relat_1(C_63)) | ~v1_funct_1(C_63) | ~v1_relat_1(C_63) | ~v1_funct_1(B_64) | ~v1_relat_1(B_64))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.97/1.44  tff(c_324, plain, (![B_64]: (r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'), k1_relat_1(k5_relat_1('#skF_6', B_64))) | ~r2_hidden('#skF_5', k1_relat_1(B_64)) | ~r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'), k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_funct_1(B_64) | ~v1_relat_1(B_64))), inference(superposition, [status(thm), theory('equality')], [c_160, c_306])).
% 2.97/1.44  tff(c_328, plain, (![B_64]: (r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'), k1_relat_1(k5_relat_1('#skF_6', B_64))) | ~r2_hidden('#skF_5', k1_relat_1(B_64)) | ~r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'), k1_relat_1('#skF_6')) | ~v1_funct_1(B_64) | ~v1_relat_1(B_64))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_324])).
% 2.97/1.44  tff(c_340, plain, (~r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'), k1_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_328])).
% 2.97/1.44  tff(c_343, plain, (~r2_hidden('#skF_5', k2_relat_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_36, c_340])).
% 2.97/1.44  tff(c_349, plain, (~v1_funct_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_219, c_44, c_343])).
% 2.97/1.44  tff(c_356, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2, c_349])).
% 2.97/1.44  tff(c_360, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_356])).
% 2.97/1.44  tff(c_362, plain, (r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'), k1_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_328])).
% 2.97/1.44  tff(c_6, plain, (![A_2, C_5, B_3]: (r2_hidden(A_2, k1_relat_1(k5_relat_1(C_5, B_3))) | ~r2_hidden(k1_funct_1(C_5, A_2), k1_relat_1(B_3)) | ~r2_hidden(A_2, k1_relat_1(C_5)) | ~v1_funct_1(C_5) | ~v1_relat_1(C_5) | ~v1_funct_1(B_3) | ~v1_relat_1(B_3))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.97/1.44  tff(c_365, plain, (r2_hidden('#skF_5', k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'))) | ~r2_hidden('#skF_5', k1_relat_1(k2_funct_1('#skF_6'))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_362, c_6])).
% 2.97/1.44  tff(c_368, plain, (r2_hidden('#skF_5', k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'))) | ~r2_hidden('#skF_5', k1_relat_1(k2_funct_1('#skF_6'))) | ~v1_funct_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_219, c_365])).
% 2.97/1.44  tff(c_369, plain, (~v1_funct_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_368])).
% 2.97/1.44  tff(c_372, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2, c_369])).
% 2.97/1.44  tff(c_376, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_372])).
% 2.97/1.44  tff(c_378, plain, (v1_funct_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_368])).
% 2.97/1.44  tff(c_165, plain, (![A_44]: (k1_relat_1(k2_funct_1(A_44))=k2_relat_1(A_44) | ~v1_funct_1(k2_funct_1(A_44)) | ~v1_relat_1(k2_funct_1(A_44)) | ~v2_funct_1(A_44) | ~v1_funct_1(A_44) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.97/1.44  tff(c_170, plain, (![A_45]: (k1_relat_1(k2_funct_1(A_45))=k2_relat_1(A_45) | ~v1_funct_1(k2_funct_1(A_45)) | ~v2_funct_1(A_45) | ~v1_funct_1(A_45) | ~v1_relat_1(A_45))), inference(resolution, [status(thm)], [c_4, c_165])).
% 2.97/1.44  tff(c_174, plain, (![A_1]: (k1_relat_1(k2_funct_1(A_1))=k2_relat_1(A_1) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(resolution, [status(thm)], [c_2, c_170])).
% 2.97/1.44  tff(c_377, plain, (~r2_hidden('#skF_5', k1_relat_1(k2_funct_1('#skF_6'))) | r2_hidden('#skF_5', k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6')))), inference(splitRight, [status(thm)], [c_368])).
% 2.97/1.44  tff(c_380, plain, (~r2_hidden('#skF_5', k1_relat_1(k2_funct_1('#skF_6')))), inference(splitLeft, [status(thm)], [c_377])).
% 2.97/1.44  tff(c_383, plain, (~r2_hidden('#skF_5', k2_relat_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_174, c_380])).
% 2.97/1.44  tff(c_386, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_383])).
% 2.97/1.44  tff(c_387, plain, (r2_hidden('#skF_5', k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6')))), inference(splitRight, [status(thm)], [c_377])).
% 2.97/1.44  tff(c_12, plain, (![C_9, B_7, A_6]: (k1_funct_1(k5_relat_1(C_9, B_7), A_6)=k1_funct_1(B_7, k1_funct_1(C_9, A_6)) | ~r2_hidden(A_6, k1_relat_1(k5_relat_1(C_9, B_7))) | ~v1_funct_1(C_9) | ~v1_relat_1(C_9) | ~v1_funct_1(B_7) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.97/1.44  tff(c_419, plain, (k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'), '#skF_5')=k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), '#skF_5')) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_387, c_12])).
% 2.97/1.44  tff(c_425, plain, (k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'), '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_219, c_378, c_160, c_419])).
% 2.97/1.44  tff(c_427, plain, $false, inference(negUnitSimplification, [status(thm)], [c_159, c_425])).
% 2.97/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.44  
% 2.97/1.44  Inference rules
% 2.97/1.44  ----------------------
% 2.97/1.44  #Ref     : 0
% 2.97/1.44  #Sup     : 77
% 2.97/1.44  #Fact    : 0
% 2.97/1.44  #Define  : 0
% 2.97/1.44  #Split   : 7
% 2.97/1.44  #Chain   : 0
% 2.97/1.44  #Close   : 0
% 2.97/1.44  
% 2.97/1.44  Ordering : KBO
% 2.97/1.44  
% 2.97/1.44  Simplification rules
% 2.97/1.44  ----------------------
% 2.97/1.44  #Subsume      : 4
% 2.97/1.44  #Demod        : 69
% 2.97/1.44  #Tautology    : 29
% 2.97/1.44  #SimpNegUnit  : 1
% 2.97/1.44  #BackRed      : 0
% 2.97/1.44  
% 2.97/1.44  #Partial instantiations: 0
% 2.97/1.44  #Strategies tried      : 1
% 2.97/1.44  
% 2.97/1.44  Timing (in seconds)
% 2.97/1.44  ----------------------
% 2.97/1.44  Preprocessing        : 0.35
% 2.97/1.44  Parsing              : 0.18
% 2.97/1.44  CNF conversion       : 0.03
% 2.97/1.44  Main loop            : 0.32
% 2.97/1.44  Inferencing          : 0.12
% 2.97/1.44  Reduction            : 0.09
% 2.97/1.44  Demodulation         : 0.07
% 2.97/1.44  BG Simplification    : 0.03
% 2.97/1.44  Subsumption          : 0.06
% 2.97/1.44  Abstraction          : 0.02
% 2.97/1.44  MUC search           : 0.00
% 2.97/1.44  Cooper               : 0.00
% 2.97/1.44  Total                : 0.70
% 2.97/1.44  Index Insertion      : 0.00
% 2.97/1.44  Index Deletion       : 0.00
% 2.97/1.44  Index Matching       : 0.00
% 2.97/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
