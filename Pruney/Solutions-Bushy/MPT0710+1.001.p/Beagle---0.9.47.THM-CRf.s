%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0710+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:44 EST 2020

% Result     : Theorem 8.65s
% Output     : CNFRefutation 8.77s
% Verified   : 
% Statistics : Number of formulae       :  138 (1196 expanded)
%              Number of leaves         :   23 ( 411 expanded)
%              Depth                    :   17
%              Number of atoms          :  376 (3505 expanded)
%              Number of equality atoms :  120 (1236 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k7_relat_1 > k3_xboole_0 > k1_funct_1 > #nlpp > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_90,negated_conjecture,(
    ~ ! [A] :
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

tff(f_34,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_26,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k1_relat_1(A) = k1_relat_1(B)
              & ! [C] :
                  ( r2_hidden(C,k1_relat_1(A))
                 => k1_funct_1(A,C) = k1_funct_1(B,C) ) )
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,B)
       => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_funct_1)).

tff(c_32,plain,
    ( r2_hidden('#skF_5','#skF_4')
    | k7_relat_1('#skF_2','#skF_4') != k7_relat_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_87,plain,(
    k7_relat_1('#skF_2','#skF_4') != k7_relat_1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_28,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_26,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( v1_relat_1(k7_relat_1(A_3,B_4))
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_94,plain,(
    ! [B_45,A_46] :
      ( k3_xboole_0(k1_relat_1(B_45),A_46) = k1_relat_1(k7_relat_1(B_45,A_46))
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_117,plain,(
    ! [A_47,B_48] :
      ( k3_xboole_0(A_47,k1_relat_1(B_48)) = k1_relat_1(k7_relat_1(B_48,A_47))
      | ~ v1_relat_1(B_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_2])).

tff(c_20,plain,(
    r1_tarski('#skF_4',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_74,plain,(
    ! [A_39,B_40] :
      ( k3_xboole_0(A_39,B_40) = A_39
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_82,plain,(
    k3_xboole_0('#skF_4',k1_relat_1('#skF_2')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_20,c_74])).

tff(c_127,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_4')) = '#skF_4'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_82])).

tff(c_160,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_127])).

tff(c_100,plain,(
    ! [A_46,B_45] :
      ( k3_xboole_0(A_46,k1_relat_1(B_45)) = k1_relat_1(k7_relat_1(B_45,A_46))
      | ~ v1_relat_1(B_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_2])).

tff(c_171,plain,(
    ! [A_46] :
      ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_4'),A_46)) = k3_xboole_0(A_46,'#skF_4')
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_100])).

tff(c_2747,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_171])).

tff(c_2759,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_2747])).

tff(c_2763,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_2759])).

tff(c_2765,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_171])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( v1_funct_1(k7_relat_1(A_3,B_4))
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2984,plain,(
    ! [A_129,B_130] :
      ( r2_hidden('#skF_1'(A_129,B_130),k1_relat_1(A_129))
      | B_130 = A_129
      | k1_relat_1(B_130) != k1_relat_1(A_129)
      | ~ v1_funct_1(B_130)
      | ~ v1_relat_1(B_130)
      | ~ v1_funct_1(A_129)
      | ~ v1_relat_1(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_3005,plain,(
    ! [B_130] :
      ( r2_hidden('#skF_1'(k7_relat_1('#skF_2','#skF_4'),B_130),'#skF_4')
      | k7_relat_1('#skF_2','#skF_4') = B_130
      | k1_relat_1(k7_relat_1('#skF_2','#skF_4')) != k1_relat_1(B_130)
      | ~ v1_funct_1(B_130)
      | ~ v1_relat_1(B_130)
      | ~ v1_funct_1(k7_relat_1('#skF_2','#skF_4'))
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_2984])).

tff(c_3011,plain,(
    ! [B_130] :
      ( r2_hidden('#skF_1'(k7_relat_1('#skF_2','#skF_4'),B_130),'#skF_4')
      | k7_relat_1('#skF_2','#skF_4') = B_130
      | k1_relat_1(B_130) != '#skF_4'
      | ~ v1_funct_1(B_130)
      | ~ v1_relat_1(B_130)
      | ~ v1_funct_1(k7_relat_1('#skF_2','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2765,c_160,c_3005])).

tff(c_3171,plain,(
    ~ v1_funct_1(k7_relat_1('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_3011])).

tff(c_3174,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_3171])).

tff(c_3178,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_3174])).

tff(c_3180,plain,(
    v1_funct_1(k7_relat_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_3011])).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_22,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_18,plain,(
    r1_tarski('#skF_4',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_81,plain,(
    k3_xboole_0('#skF_4',k1_relat_1('#skF_3')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_18,c_74])).

tff(c_149,plain,
    ( k1_relat_1(k7_relat_1('#skF_3','#skF_4')) = '#skF_4'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_117])).

tff(c_167,plain,(
    k1_relat_1(k7_relat_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_149])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( k3_xboole_0(k1_relat_1(B_11),A_10) = k1_relat_1(k7_relat_1(B_11,A_10))
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_184,plain,(
    ! [A_10] :
      ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_3','#skF_4'),A_10)) = k3_xboole_0('#skF_4',A_10)
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_12])).

tff(c_2722,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_184])).

tff(c_2725,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_2722])).

tff(c_2729,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_2725])).

tff(c_2731,plain,(
    v1_relat_1(k7_relat_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_3002,plain,(
    ! [B_130] :
      ( r2_hidden('#skF_1'(k7_relat_1('#skF_3','#skF_4'),B_130),'#skF_4')
      | k7_relat_1('#skF_3','#skF_4') = B_130
      | k1_relat_1(k7_relat_1('#skF_3','#skF_4')) != k1_relat_1(B_130)
      | ~ v1_funct_1(B_130)
      | ~ v1_relat_1(B_130)
      | ~ v1_funct_1(k7_relat_1('#skF_3','#skF_4'))
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_2984])).

tff(c_3009,plain,(
    ! [B_130] :
      ( r2_hidden('#skF_1'(k7_relat_1('#skF_3','#skF_4'),B_130),'#skF_4')
      | k7_relat_1('#skF_3','#skF_4') = B_130
      | k1_relat_1(B_130) != '#skF_4'
      | ~ v1_funct_1(B_130)
      | ~ v1_relat_1(B_130)
      | ~ v1_funct_1(k7_relat_1('#skF_3','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2731,c_167,c_3002])).

tff(c_3156,plain,(
    ~ v1_funct_1(k7_relat_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_3009])).

tff(c_3159,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_3156])).

tff(c_3163,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_3159])).

tff(c_3164,plain,(
    ! [B_130] :
      ( r2_hidden('#skF_1'(k7_relat_1('#skF_3','#skF_4'),B_130),'#skF_4')
      | k7_relat_1('#skF_3','#skF_4') = B_130
      | k1_relat_1(B_130) != '#skF_4'
      | ~ v1_funct_1(B_130)
      | ~ v1_relat_1(B_130) ) ),
    inference(splitRight,[status(thm)],[c_3009])).

tff(c_3165,plain,(
    v1_funct_1(k7_relat_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_3009])).

tff(c_3166,plain,(
    ! [B_137] :
      ( r2_hidden('#skF_1'(k7_relat_1('#skF_3','#skF_4'),B_137),'#skF_4')
      | k7_relat_1('#skF_3','#skF_4') = B_137
      | k1_relat_1(B_137) != '#skF_4'
      | ~ v1_funct_1(B_137)
      | ~ v1_relat_1(B_137) ) ),
    inference(splitRight,[status(thm)],[c_3009])).

tff(c_174,plain,(
    ! [A_10] :
      ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_4'),A_10)) = k3_xboole_0('#skF_4',A_10)
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_12])).

tff(c_251,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_174])).

tff(c_254,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_251])).

tff(c_258,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_254])).

tff(c_260,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_174])).

tff(c_278,plain,(
    ! [A_56,B_57] :
      ( r2_hidden('#skF_1'(A_56,B_57),k1_relat_1(A_56))
      | B_57 = A_56
      | k1_relat_1(B_57) != k1_relat_1(A_56)
      | ~ v1_funct_1(B_57)
      | ~ v1_relat_1(B_57)
      | ~ v1_funct_1(A_56)
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_290,plain,(
    ! [B_57] :
      ( r2_hidden('#skF_1'(k7_relat_1('#skF_2','#skF_4'),B_57),'#skF_4')
      | k7_relat_1('#skF_2','#skF_4') = B_57
      | k1_relat_1(k7_relat_1('#skF_2','#skF_4')) != k1_relat_1(B_57)
      | ~ v1_funct_1(B_57)
      | ~ v1_relat_1(B_57)
      | ~ v1_funct_1(k7_relat_1('#skF_2','#skF_4'))
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_278])).

tff(c_296,plain,(
    ! [B_57] :
      ( r2_hidden('#skF_1'(k7_relat_1('#skF_2','#skF_4'),B_57),'#skF_4')
      | k7_relat_1('#skF_2','#skF_4') = B_57
      | k1_relat_1(B_57) != '#skF_4'
      | ~ v1_funct_1(B_57)
      | ~ v1_relat_1(B_57)
      | ~ v1_funct_1(k7_relat_1('#skF_2','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_160,c_290])).

tff(c_669,plain,(
    ~ v1_funct_1(k7_relat_1('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_296])).

tff(c_672,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_669])).

tff(c_676,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_672])).

tff(c_678,plain,(
    v1_funct_1(k7_relat_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_296])).

tff(c_214,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_184])).

tff(c_217,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_214])).

tff(c_221,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_217])).

tff(c_223,plain,(
    v1_relat_1(k7_relat_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_287,plain,(
    ! [B_57] :
      ( r2_hidden('#skF_1'(k7_relat_1('#skF_3','#skF_4'),B_57),'#skF_4')
      | k7_relat_1('#skF_3','#skF_4') = B_57
      | k1_relat_1(k7_relat_1('#skF_3','#skF_4')) != k1_relat_1(B_57)
      | ~ v1_funct_1(B_57)
      | ~ v1_relat_1(B_57)
      | ~ v1_funct_1(k7_relat_1('#skF_3','#skF_4'))
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_278])).

tff(c_294,plain,(
    ! [B_57] :
      ( r2_hidden('#skF_1'(k7_relat_1('#skF_3','#skF_4'),B_57),'#skF_4')
      | k7_relat_1('#skF_3','#skF_4') = B_57
      | k1_relat_1(B_57) != '#skF_4'
      | ~ v1_funct_1(B_57)
      | ~ v1_relat_1(B_57)
      | ~ v1_funct_1(k7_relat_1('#skF_3','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_167,c_287])).

tff(c_496,plain,(
    ~ v1_funct_1(k7_relat_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_294])).

tff(c_499,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_496])).

tff(c_503,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_499])).

tff(c_504,plain,(
    ! [B_57] :
      ( r2_hidden('#skF_1'(k7_relat_1('#skF_3','#skF_4'),B_57),'#skF_4')
      | k7_relat_1('#skF_3','#skF_4') = B_57
      | k1_relat_1(B_57) != '#skF_4'
      | ~ v1_funct_1(B_57)
      | ~ v1_relat_1(B_57) ) ),
    inference(splitRight,[status(thm)],[c_294])).

tff(c_505,plain,(
    v1_funct_1(k7_relat_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_294])).

tff(c_506,plain,(
    ! [B_62] :
      ( r2_hidden('#skF_1'(k7_relat_1('#skF_3','#skF_4'),B_62),'#skF_4')
      | k7_relat_1('#skF_3','#skF_4') = B_62
      | k1_relat_1(B_62) != '#skF_4'
      | ~ v1_funct_1(B_62)
      | ~ v1_relat_1(B_62) ) ),
    inference(splitRight,[status(thm)],[c_294])).

tff(c_36,plain,(
    ! [D_36] :
      ( k1_funct_1('#skF_2','#skF_5') != k1_funct_1('#skF_3','#skF_5')
      | k1_funct_1('#skF_2',D_36) = k1_funct_1('#skF_3',D_36)
      | ~ r2_hidden(D_36,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_191,plain,(
    k1_funct_1('#skF_2','#skF_5') != k1_funct_1('#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_38,plain,(
    ! [D_36] :
      ( r2_hidden('#skF_5','#skF_4')
      | k1_funct_1('#skF_2',D_36) = k1_funct_1('#skF_3',D_36)
      | ~ r2_hidden(D_36,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_188,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_40,plain,(
    ! [D_36] :
      ( k7_relat_1('#skF_2','#skF_4') = k7_relat_1('#skF_3','#skF_4')
      | k1_funct_1('#skF_2',D_36) = k1_funct_1('#skF_3',D_36)
      | ~ r2_hidden(D_36,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_194,plain,(
    ! [D_49] :
      ( k1_funct_1('#skF_2',D_49) = k1_funct_1('#skF_3',D_49)
      | ~ r2_hidden(D_49,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_40])).

tff(c_197,plain,(
    k1_funct_1('#skF_2','#skF_5') = k1_funct_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_188,c_194])).

tff(c_201,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_191,c_197])).

tff(c_202,plain,(
    ! [D_36] :
      ( k1_funct_1('#skF_2',D_36) = k1_funct_1('#skF_3',D_36)
      | ~ r2_hidden(D_36,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_510,plain,(
    ! [B_62] :
      ( k1_funct_1('#skF_2','#skF_1'(k7_relat_1('#skF_3','#skF_4'),B_62)) = k1_funct_1('#skF_3','#skF_1'(k7_relat_1('#skF_3','#skF_4'),B_62))
      | k7_relat_1('#skF_3','#skF_4') = B_62
      | k1_relat_1(B_62) != '#skF_4'
      | ~ v1_funct_1(B_62)
      | ~ v1_relat_1(B_62) ) ),
    inference(resolution,[status(thm)],[c_506,c_202])).

tff(c_10,plain,(
    ! [C_9,B_8,A_7] :
      ( k1_funct_1(k7_relat_1(C_9,B_8),A_7) = k1_funct_1(C_9,A_7)
      | ~ r2_hidden(A_7,B_8)
      | ~ v1_funct_1(C_9)
      | ~ v1_relat_1(C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_610,plain,(
    ! [B_67,A_68] :
      ( k1_funct_1(B_67,'#skF_1'(A_68,B_67)) != k1_funct_1(A_68,'#skF_1'(A_68,B_67))
      | B_67 = A_68
      | k1_relat_1(B_67) != k1_relat_1(A_68)
      | ~ v1_funct_1(B_67)
      | ~ v1_relat_1(B_67)
      | ~ v1_funct_1(A_68)
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1346,plain,(
    ! [C_86,A_87,B_88] :
      ( k1_funct_1(C_86,'#skF_1'(A_87,k7_relat_1(C_86,B_88))) != k1_funct_1(A_87,'#skF_1'(A_87,k7_relat_1(C_86,B_88)))
      | k7_relat_1(C_86,B_88) = A_87
      | k1_relat_1(k7_relat_1(C_86,B_88)) != k1_relat_1(A_87)
      | ~ v1_funct_1(k7_relat_1(C_86,B_88))
      | ~ v1_relat_1(k7_relat_1(C_86,B_88))
      | ~ v1_funct_1(A_87)
      | ~ v1_relat_1(A_87)
      | ~ r2_hidden('#skF_1'(A_87,k7_relat_1(C_86,B_88)),B_88)
      | ~ v1_funct_1(C_86)
      | ~ v1_relat_1(C_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_610])).

tff(c_2543,plain,(
    ! [C_111,C_109,B_110,B_112] :
      ( k1_funct_1(C_111,'#skF_1'(k7_relat_1(C_109,B_110),k7_relat_1(C_111,B_112))) != k1_funct_1(C_109,'#skF_1'(k7_relat_1(C_109,B_110),k7_relat_1(C_111,B_112)))
      | k7_relat_1(C_111,B_112) = k7_relat_1(C_109,B_110)
      | k1_relat_1(k7_relat_1(C_111,B_112)) != k1_relat_1(k7_relat_1(C_109,B_110))
      | ~ v1_funct_1(k7_relat_1(C_111,B_112))
      | ~ v1_relat_1(k7_relat_1(C_111,B_112))
      | ~ v1_funct_1(k7_relat_1(C_109,B_110))
      | ~ v1_relat_1(k7_relat_1(C_109,B_110))
      | ~ r2_hidden('#skF_1'(k7_relat_1(C_109,B_110),k7_relat_1(C_111,B_112)),B_112)
      | ~ v1_funct_1(C_111)
      | ~ v1_relat_1(C_111)
      | ~ r2_hidden('#skF_1'(k7_relat_1(C_109,B_110),k7_relat_1(C_111,B_112)),B_110)
      | ~ v1_funct_1(C_109)
      | ~ v1_relat_1(C_109) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1346])).

tff(c_2549,plain,(
    ! [B_112] :
      ( k1_relat_1(k7_relat_1('#skF_2',B_112)) != k1_relat_1(k7_relat_1('#skF_3','#skF_4'))
      | ~ v1_funct_1(k7_relat_1('#skF_3','#skF_4'))
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_4'))
      | ~ r2_hidden('#skF_1'(k7_relat_1('#skF_3','#skF_4'),k7_relat_1('#skF_2',B_112)),B_112)
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | ~ r2_hidden('#skF_1'(k7_relat_1('#skF_3','#skF_4'),k7_relat_1('#skF_2',B_112)),'#skF_4')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | k7_relat_1('#skF_2',B_112) = k7_relat_1('#skF_3','#skF_4')
      | k1_relat_1(k7_relat_1('#skF_2',B_112)) != '#skF_4'
      | ~ v1_funct_1(k7_relat_1('#skF_2',B_112))
      | ~ v1_relat_1(k7_relat_1('#skF_2',B_112)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_510,c_2543])).

tff(c_2693,plain,(
    ! [B_115] :
      ( ~ r2_hidden('#skF_1'(k7_relat_1('#skF_3','#skF_4'),k7_relat_1('#skF_2',B_115)),B_115)
      | ~ r2_hidden('#skF_1'(k7_relat_1('#skF_3','#skF_4'),k7_relat_1('#skF_2',B_115)),'#skF_4')
      | k7_relat_1('#skF_2',B_115) = k7_relat_1('#skF_3','#skF_4')
      | k1_relat_1(k7_relat_1('#skF_2',B_115)) != '#skF_4'
      | ~ v1_funct_1(k7_relat_1('#skF_2',B_115))
      | ~ v1_relat_1(k7_relat_1('#skF_2',B_115)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_28,c_26,c_223,c_505,c_167,c_2549])).

tff(c_2696,plain,
    ( ~ r2_hidden('#skF_1'(k7_relat_1('#skF_3','#skF_4'),k7_relat_1('#skF_2','#skF_4')),'#skF_4')
    | k7_relat_1('#skF_2','#skF_4') = k7_relat_1('#skF_3','#skF_4')
    | k1_relat_1(k7_relat_1('#skF_2','#skF_4')) != '#skF_4'
    | ~ v1_funct_1(k7_relat_1('#skF_2','#skF_4'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_504,c_2693])).

tff(c_2702,plain,
    ( ~ r2_hidden('#skF_1'(k7_relat_1('#skF_3','#skF_4'),k7_relat_1('#skF_2','#skF_4')),'#skF_4')
    | k7_relat_1('#skF_2','#skF_4') = k7_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_678,c_160,c_2696])).

tff(c_2703,plain,(
    ~ r2_hidden('#skF_1'(k7_relat_1('#skF_3','#skF_4'),k7_relat_1('#skF_2','#skF_4')),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_2702])).

tff(c_2710,plain,
    ( k7_relat_1('#skF_2','#skF_4') = k7_relat_1('#skF_3','#skF_4')
    | k1_relat_1(k7_relat_1('#skF_2','#skF_4')) != '#skF_4'
    | ~ v1_funct_1(k7_relat_1('#skF_2','#skF_4'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_504,c_2703])).

tff(c_2713,plain,(
    k7_relat_1('#skF_2','#skF_4') = k7_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_678,c_160,c_2710])).

tff(c_2715,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_2713])).

tff(c_2716,plain,(
    ! [D_36] :
      ( k1_funct_1('#skF_2',D_36) = k1_funct_1('#skF_3',D_36)
      | ~ r2_hidden(D_36,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_3170,plain,(
    ! [B_137] :
      ( k1_funct_1('#skF_2','#skF_1'(k7_relat_1('#skF_3','#skF_4'),B_137)) = k1_funct_1('#skF_3','#skF_1'(k7_relat_1('#skF_3','#skF_4'),B_137))
      | k7_relat_1('#skF_3','#skF_4') = B_137
      | k1_relat_1(B_137) != '#skF_4'
      | ~ v1_funct_1(B_137)
      | ~ v1_relat_1(B_137) ) ),
    inference(resolution,[status(thm)],[c_3166,c_2716])).

tff(c_3186,plain,(
    ! [B_138,A_139] :
      ( k1_funct_1(B_138,'#skF_1'(A_139,B_138)) != k1_funct_1(A_139,'#skF_1'(A_139,B_138))
      | B_138 = A_139
      | k1_relat_1(B_138) != k1_relat_1(A_139)
      | ~ v1_funct_1(B_138)
      | ~ v1_relat_1(B_138)
      | ~ v1_funct_1(A_139)
      | ~ v1_relat_1(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_3504,plain,(
    ! [C_149,B_150,B_151] :
      ( k1_funct_1(C_149,'#skF_1'(k7_relat_1(C_149,B_150),B_151)) != k1_funct_1(B_151,'#skF_1'(k7_relat_1(C_149,B_150),B_151))
      | k7_relat_1(C_149,B_150) = B_151
      | k1_relat_1(k7_relat_1(C_149,B_150)) != k1_relat_1(B_151)
      | ~ v1_funct_1(B_151)
      | ~ v1_relat_1(B_151)
      | ~ v1_funct_1(k7_relat_1(C_149,B_150))
      | ~ v1_relat_1(k7_relat_1(C_149,B_150))
      | ~ r2_hidden('#skF_1'(k7_relat_1(C_149,B_150),B_151),B_150)
      | ~ v1_funct_1(C_149)
      | ~ v1_relat_1(C_149) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_3186])).

tff(c_5152,plain,(
    ! [C_182,B_183,C_181,B_184] :
      ( k1_funct_1(C_182,'#skF_1'(k7_relat_1(C_182,B_183),k7_relat_1(C_181,B_184))) != k1_funct_1(C_181,'#skF_1'(k7_relat_1(C_182,B_183),k7_relat_1(C_181,B_184)))
      | k7_relat_1(C_182,B_183) = k7_relat_1(C_181,B_184)
      | k1_relat_1(k7_relat_1(C_182,B_183)) != k1_relat_1(k7_relat_1(C_181,B_184))
      | ~ v1_funct_1(k7_relat_1(C_181,B_184))
      | ~ v1_relat_1(k7_relat_1(C_181,B_184))
      | ~ v1_funct_1(k7_relat_1(C_182,B_183))
      | ~ v1_relat_1(k7_relat_1(C_182,B_183))
      | ~ r2_hidden('#skF_1'(k7_relat_1(C_182,B_183),k7_relat_1(C_181,B_184)),B_183)
      | ~ v1_funct_1(C_182)
      | ~ v1_relat_1(C_182)
      | ~ r2_hidden('#skF_1'(k7_relat_1(C_182,B_183),k7_relat_1(C_181,B_184)),B_184)
      | ~ v1_funct_1(C_181)
      | ~ v1_relat_1(C_181) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_3504])).

tff(c_5158,plain,(
    ! [B_184] :
      ( k1_relat_1(k7_relat_1('#skF_2',B_184)) != k1_relat_1(k7_relat_1('#skF_3','#skF_4'))
      | ~ v1_funct_1(k7_relat_1('#skF_3','#skF_4'))
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_4'))
      | ~ r2_hidden('#skF_1'(k7_relat_1('#skF_3','#skF_4'),k7_relat_1('#skF_2',B_184)),'#skF_4')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ r2_hidden('#skF_1'(k7_relat_1('#skF_3','#skF_4'),k7_relat_1('#skF_2',B_184)),B_184)
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | k7_relat_1('#skF_2',B_184) = k7_relat_1('#skF_3','#skF_4')
      | k1_relat_1(k7_relat_1('#skF_2',B_184)) != '#skF_4'
      | ~ v1_funct_1(k7_relat_1('#skF_2',B_184))
      | ~ v1_relat_1(k7_relat_1('#skF_2',B_184)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3170,c_5152])).

tff(c_6069,plain,(
    ! [B_190] :
      ( ~ r2_hidden('#skF_1'(k7_relat_1('#skF_3','#skF_4'),k7_relat_1('#skF_2',B_190)),'#skF_4')
      | ~ r2_hidden('#skF_1'(k7_relat_1('#skF_3','#skF_4'),k7_relat_1('#skF_2',B_190)),B_190)
      | k7_relat_1('#skF_2',B_190) = k7_relat_1('#skF_3','#skF_4')
      | k1_relat_1(k7_relat_1('#skF_2',B_190)) != '#skF_4'
      | ~ v1_funct_1(k7_relat_1('#skF_2',B_190))
      | ~ v1_relat_1(k7_relat_1('#skF_2',B_190)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_22,c_2731,c_3165,c_167,c_5158])).

tff(c_8171,plain,(
    ! [B_218] :
      ( ~ r2_hidden('#skF_1'(k7_relat_1('#skF_3','#skF_4'),k7_relat_1('#skF_2',B_218)),B_218)
      | k7_relat_1('#skF_2',B_218) = k7_relat_1('#skF_3','#skF_4')
      | k1_relat_1(k7_relat_1('#skF_2',B_218)) != '#skF_4'
      | ~ v1_funct_1(k7_relat_1('#skF_2',B_218))
      | ~ v1_relat_1(k7_relat_1('#skF_2',B_218)) ) ),
    inference(resolution,[status(thm)],[c_3164,c_6069])).

tff(c_8175,plain,
    ( k7_relat_1('#skF_2','#skF_4') = k7_relat_1('#skF_3','#skF_4')
    | k1_relat_1(k7_relat_1('#skF_2','#skF_4')) != '#skF_4'
    | ~ v1_funct_1(k7_relat_1('#skF_2','#skF_4'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_3164,c_8171])).

tff(c_8182,plain,(
    k7_relat_1('#skF_2','#skF_4') = k7_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2765,c_3180,c_160,c_8175])).

tff(c_8184,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_8182])).

tff(c_8186,plain,(
    k7_relat_1('#skF_2','#skF_4') = k7_relat_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_30,plain,
    ( k1_funct_1('#skF_2','#skF_5') != k1_funct_1('#skF_3','#skF_5')
    | k7_relat_1('#skF_2','#skF_4') != k7_relat_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_8315,plain,(
    k1_funct_1('#skF_2','#skF_5') != k1_funct_1('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8186,c_30])).

tff(c_8185,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_8477,plain,(
    ! [C_231,B_232,A_233] :
      ( k1_funct_1(k7_relat_1(C_231,B_232),A_233) = k1_funct_1(C_231,A_233)
      | ~ r2_hidden(A_233,B_232)
      | ~ v1_funct_1(C_231)
      | ~ v1_relat_1(C_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_8486,plain,(
    ! [A_233] :
      ( k1_funct_1(k7_relat_1('#skF_3','#skF_4'),A_233) = k1_funct_1('#skF_2',A_233)
      | ~ r2_hidden(A_233,'#skF_4')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8186,c_8477])).

tff(c_8491,plain,(
    ! [A_234] :
      ( k1_funct_1(k7_relat_1('#skF_3','#skF_4'),A_234) = k1_funct_1('#skF_2',A_234)
      | ~ r2_hidden(A_234,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_8486])).

tff(c_8497,plain,(
    ! [A_234] :
      ( k1_funct_1('#skF_2',A_234) = k1_funct_1('#skF_3',A_234)
      | ~ r2_hidden(A_234,'#skF_4')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ r2_hidden(A_234,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8491,c_10])).

tff(c_8511,plain,(
    ! [A_235] :
      ( k1_funct_1('#skF_2',A_235) = k1_funct_1('#skF_3',A_235)
      | ~ r2_hidden(A_235,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_8497])).

tff(c_8514,plain,(
    k1_funct_1('#skF_2','#skF_5') = k1_funct_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_8185,c_8511])).

tff(c_8518,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8315,c_8514])).

%------------------------------------------------------------------------------
