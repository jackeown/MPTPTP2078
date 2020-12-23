%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:26 EST 2020

% Result     : Theorem 6.40s
% Output     : CNFRefutation 6.66s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 630 expanded)
%              Number of leaves         :   24 ( 200 expanded)
%              Depth                    :   16
%              Number of atoms          :  262 (1817 expanded)
%              Number of equality atoms :   41 ( 486 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_ordinal1 > v4_ordinal1 > v3_ordinal1 > v1_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v4_ordinal1,type,(
    v4_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_106,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ( ~ ( ~ v4_ordinal1(A)
              & ! [B] :
                  ( v3_ordinal1(B)
                 => A != k1_ordinal1(B) ) )
          & ~ ( ? [B] :
                  ( v3_ordinal1(B)
                  & A = k1_ordinal1(B) )
              & v4_ordinal1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_ordinal1)).

tff(f_85,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v4_ordinal1(A)
      <=> ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(B,A)
             => r2_hidden(k1_ordinal1(B),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_ordinal1)).

tff(f_41,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( ~ v1_xboole_0(k1_ordinal1(A))
        & v3_ordinal1(k1_ordinal1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_ordinal1)).

tff(f_65,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_hidden(A,B)
          <=> r1_ordinal1(k1_ordinal1(A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

tff(f_74,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_hidden(A,k1_ordinal1(B))
          <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_50,axiom,(
    ! [A] : A != k1_ordinal1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_ordinal1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(c_42,plain,(
    v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_40,plain,(
    ! [A_17] :
      ( v3_ordinal1('#skF_3'(A_17))
      | v4_ordinal1(A_17)
      | ~ v3_ordinal1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_38,plain,(
    ! [A_17] :
      ( r2_hidden('#skF_3'(A_17),A_17)
      | v4_ordinal1(A_17)
      | ~ v3_ordinal1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_12,plain,(
    ! [A_5] :
      ( v3_ordinal1(k1_ordinal1(A_5))
      | ~ v3_ordinal1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_28,plain,(
    ! [A_11,B_13] :
      ( r1_ordinal1(k1_ordinal1(A_11),B_13)
      | ~ r2_hidden(A_11,B_13)
      | ~ v3_ordinal1(B_13)
      | ~ v3_ordinal1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_131,plain,(
    ! [A_44,B_45] :
      ( r2_hidden(A_44,k1_ordinal1(B_45))
      | ~ r1_ordinal1(A_44,B_45)
      | ~ v3_ordinal1(B_45)
      | ~ v3_ordinal1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_16,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | r2_hidden(A_6,B_7)
      | ~ r2_hidden(A_6,k1_ordinal1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_329,plain,(
    ! [B_68,A_69] :
      ( B_68 = A_69
      | r2_hidden(A_69,B_68)
      | ~ r1_ordinal1(A_69,B_68)
      | ~ v3_ordinal1(B_68)
      | ~ v3_ordinal1(A_69) ) ),
    inference(resolution,[status(thm)],[c_131,c_16])).

tff(c_36,plain,(
    ! [A_17] :
      ( ~ r2_hidden(k1_ordinal1('#skF_3'(A_17)),A_17)
      | v4_ordinal1(A_17)
      | ~ v3_ordinal1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_806,plain,(
    ! [B_111] :
      ( v4_ordinal1(B_111)
      | k1_ordinal1('#skF_3'(B_111)) = B_111
      | ~ r1_ordinal1(k1_ordinal1('#skF_3'(B_111)),B_111)
      | ~ v3_ordinal1(B_111)
      | ~ v3_ordinal1(k1_ordinal1('#skF_3'(B_111))) ) ),
    inference(resolution,[status(thm)],[c_329,c_36])).

tff(c_1583,plain,(
    ! [B_149] :
      ( v4_ordinal1(B_149)
      | k1_ordinal1('#skF_3'(B_149)) = B_149
      | ~ v3_ordinal1(k1_ordinal1('#skF_3'(B_149)))
      | ~ r2_hidden('#skF_3'(B_149),B_149)
      | ~ v3_ordinal1(B_149)
      | ~ v3_ordinal1('#skF_3'(B_149)) ) ),
    inference(resolution,[status(thm)],[c_28,c_806])).

tff(c_1588,plain,(
    ! [B_150] :
      ( v4_ordinal1(B_150)
      | k1_ordinal1('#skF_3'(B_150)) = B_150
      | ~ r2_hidden('#skF_3'(B_150),B_150)
      | ~ v3_ordinal1(B_150)
      | ~ v3_ordinal1('#skF_3'(B_150)) ) ),
    inference(resolution,[status(thm)],[c_12,c_1583])).

tff(c_1618,plain,(
    ! [A_151] :
      ( k1_ordinal1('#skF_3'(A_151)) = A_151
      | ~ v3_ordinal1('#skF_3'(A_151))
      | v4_ordinal1(A_151)
      | ~ v3_ordinal1(A_151) ) ),
    inference(resolution,[status(thm)],[c_38,c_1588])).

tff(c_1623,plain,(
    ! [A_152] :
      ( k1_ordinal1('#skF_3'(A_152)) = A_152
      | v4_ordinal1(A_152)
      | ~ v3_ordinal1(A_152) ) ),
    inference(resolution,[status(thm)],[c_40,c_1618])).

tff(c_80,plain,(
    ! [A_31] :
      ( v3_ordinal1('#skF_3'(A_31))
      | v4_ordinal1(A_31)
      | ~ v3_ordinal1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_54,plain,
    ( ~ v4_ordinal1('#skF_4')
    | v3_ordinal1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_57,plain,(
    ~ v4_ordinal1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_44,plain,(
    ! [B_23] :
      ( k1_ordinal1(B_23) != '#skF_4'
      | ~ v3_ordinal1(B_23)
      | v4_ordinal1('#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_69,plain,(
    ! [B_23] :
      ( k1_ordinal1(B_23) != '#skF_4'
      | ~ v3_ordinal1(B_23) ) ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_44])).

tff(c_84,plain,(
    ! [A_31] :
      ( k1_ordinal1('#skF_3'(A_31)) != '#skF_4'
      | v4_ordinal1(A_31)
      | ~ v3_ordinal1(A_31) ) ),
    inference(resolution,[status(thm)],[c_80,c_69])).

tff(c_1806,plain,(
    ! [A_152] :
      ( A_152 != '#skF_4'
      | v4_ordinal1(A_152)
      | ~ v3_ordinal1(A_152)
      | v4_ordinal1(A_152)
      | ~ v3_ordinal1(A_152) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1623,c_84])).

tff(c_1946,plain,(
    ! [A_159] :
      ( A_159 != '#skF_4'
      | ~ v3_ordinal1(A_159)
      | v4_ordinal1(A_159) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_1806])).

tff(c_1949,plain,(
    ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1946,c_57])).

tff(c_1953,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1949])).

tff(c_1954,plain,(
    v3_ordinal1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_1955,plain,(
    v4_ordinal1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_50,plain,
    ( ~ v4_ordinal1('#skF_4')
    | k1_ordinal1('#skF_5') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1959,plain,(
    k1_ordinal1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1955,c_50])).

tff(c_18,plain,(
    ! [B_7] : r2_hidden(B_7,k1_ordinal1(B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1969,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1959,c_18])).

tff(c_2203,plain,(
    ! [A_186,B_187] :
      ( r1_ordinal1(A_186,B_187)
      | ~ r2_hidden(A_186,k1_ordinal1(B_187))
      | ~ v3_ordinal1(B_187)
      | ~ v3_ordinal1(A_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2216,plain,(
    ! [A_186] :
      ( r1_ordinal1(A_186,'#skF_5')
      | ~ r2_hidden(A_186,'#skF_4')
      | ~ v3_ordinal1('#skF_5')
      | ~ v3_ordinal1(A_186) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1959,c_2203])).

tff(c_2227,plain,(
    ! [A_189] :
      ( r1_ordinal1(A_189,'#skF_5')
      | ~ r2_hidden(A_189,'#skF_4')
      | ~ v3_ordinal1(A_189) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1954,c_2216])).

tff(c_2237,plain,
    ( r1_ordinal1('#skF_5','#skF_5')
    | ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1969,c_2227])).

tff(c_2244,plain,(
    r1_ordinal1('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1954,c_2237])).

tff(c_2152,plain,(
    ! [A_183,B_184] :
      ( r2_hidden(A_183,k1_ordinal1(B_184))
      | ~ r1_ordinal1(A_183,B_184)
      | ~ v3_ordinal1(B_184)
      | ~ v3_ordinal1(A_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2169,plain,(
    ! [A_183] :
      ( r2_hidden(A_183,'#skF_4')
      | ~ r1_ordinal1(A_183,'#skF_5')
      | ~ v3_ordinal1('#skF_5')
      | ~ v3_ordinal1(A_183) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1959,c_2152])).

tff(c_2177,plain,(
    ! [A_183] :
      ( r2_hidden(A_183,'#skF_4')
      | ~ r1_ordinal1(A_183,'#skF_5')
      | ~ v3_ordinal1(A_183) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1954,c_2169])).

tff(c_2826,plain,(
    ! [B_215,A_216] :
      ( r2_hidden(k1_ordinal1(B_215),A_216)
      | ~ r2_hidden(B_215,A_216)
      | ~ v3_ordinal1(B_215)
      | ~ v4_ordinal1(A_216)
      | ~ v3_ordinal1(A_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2863,plain,(
    ! [A_216] :
      ( r2_hidden('#skF_4',A_216)
      | ~ r2_hidden('#skF_5',A_216)
      | ~ v3_ordinal1('#skF_5')
      | ~ v4_ordinal1(A_216)
      | ~ v3_ordinal1(A_216) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1959,c_2826])).

tff(c_2937,plain,(
    ! [A_218] :
      ( r2_hidden('#skF_4',A_218)
      | ~ r2_hidden('#skF_5',A_218)
      | ~ v4_ordinal1(A_218)
      | ~ v3_ordinal1(A_218) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1954,c_2863])).

tff(c_2948,plain,
    ( r2_hidden('#skF_4','#skF_4')
    | ~ v4_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ r1_ordinal1('#skF_5','#skF_5')
    | ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2177,c_2937])).

tff(c_2974,plain,(
    r2_hidden('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1954,c_2244,c_42,c_1955,c_2948])).

tff(c_2224,plain,(
    ! [A_186] :
      ( r1_ordinal1(A_186,'#skF_5')
      | ~ r2_hidden(A_186,'#skF_4')
      | ~ v3_ordinal1(A_186) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1954,c_2216])).

tff(c_2994,plain,
    ( r1_ordinal1('#skF_4','#skF_5')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2974,c_2224])).

tff(c_3006,plain,(
    r1_ordinal1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2994])).

tff(c_2313,plain,(
    ! [A_195,B_196] :
      ( r2_hidden(A_195,B_196)
      | ~ r1_ordinal1(k1_ordinal1(A_195),B_196)
      | ~ v3_ordinal1(B_196)
      | ~ v3_ordinal1(A_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2327,plain,(
    ! [B_196] :
      ( r2_hidden('#skF_5',B_196)
      | ~ r1_ordinal1('#skF_4',B_196)
      | ~ v3_ordinal1(B_196)
      | ~ v3_ordinal1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1959,c_2313])).

tff(c_2333,plain,(
    ! [B_196] :
      ( r2_hidden('#skF_5',B_196)
      | ~ r1_ordinal1('#skF_4',B_196)
      | ~ v3_ordinal1(B_196) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1954,c_2327])).

tff(c_2023,plain,(
    ! [A_170] :
      ( r2_hidden('#skF_3'(A_170),A_170)
      | v4_ordinal1(A_170)
      | ~ v3_ordinal1(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1991,plain,(
    ! [A_164,B_165] :
      ( ~ r2_hidden(A_164,B_165)
      | r2_hidden(A_164,k1_ordinal1(B_165)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1994,plain,(
    ! [A_164] :
      ( ~ r2_hidden(A_164,'#skF_5')
      | r2_hidden(A_164,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1959,c_1991])).

tff(c_2030,plain,
    ( r2_hidden('#skF_3'('#skF_5'),'#skF_4')
    | v4_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2023,c_1994])).

tff(c_2034,plain,
    ( r2_hidden('#skF_3'('#skF_5'),'#skF_4')
    | v4_ordinal1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1954,c_2030])).

tff(c_2035,plain,(
    v4_ordinal1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_2034])).

tff(c_2860,plain,(
    ! [B_215] :
      ( r2_hidden(k1_ordinal1(B_215),'#skF_4')
      | ~ r2_hidden(B_215,'#skF_5')
      | ~ v3_ordinal1(B_215)
      | ~ v4_ordinal1('#skF_5')
      | ~ v3_ordinal1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2826,c_1994])).

tff(c_2883,plain,(
    ! [B_217] :
      ( r2_hidden(k1_ordinal1(B_217),'#skF_4')
      | ~ r2_hidden(B_217,'#skF_5')
      | ~ v3_ordinal1(B_217) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1954,c_2035,c_2860])).

tff(c_2902,plain,
    ( r2_hidden('#skF_4','#skF_4')
    | ~ r2_hidden('#skF_5','#skF_5')
    | ~ v3_ordinal1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1959,c_2883])).

tff(c_2915,plain,
    ( r2_hidden('#skF_4','#skF_4')
    | ~ r2_hidden('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1954,c_2902])).

tff(c_2916,plain,(
    ~ r2_hidden('#skF_5','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_2915])).

tff(c_2922,plain,
    ( ~ r1_ordinal1('#skF_4','#skF_5')
    | ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2333,c_2916])).

tff(c_2932,plain,(
    ~ r1_ordinal1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1954,c_2922])).

tff(c_3022,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3006,c_2932])).

tff(c_3024,plain,(
    r2_hidden('#skF_5','#skF_5') ),
    inference(splitRight,[status(thm)],[c_2915])).

tff(c_22,plain,(
    ! [A_8] : k1_ordinal1(A_8) != A_8 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1972,plain,(
    '#skF_5' != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1959,c_22])).

tff(c_8,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r2_hidden('#skF_2'(A_1,B_2),A_1)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2052,plain,(
    ! [B_174,A_175] :
      ( B_174 = A_175
      | r2_hidden(A_175,B_174)
      | ~ r2_hidden(A_175,k1_ordinal1(B_174)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2062,plain,(
    ! [A_175] :
      ( A_175 = '#skF_5'
      | r2_hidden(A_175,'#skF_5')
      | ~ r2_hidden(A_175,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1959,c_2052])).

tff(c_2641,plain,(
    ! [A_209,B_210] :
      ( r2_hidden('#skF_1'(A_209,B_210),B_210)
      | ~ r2_hidden('#skF_2'(A_209,B_210),B_210)
      | B_210 = A_209 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_6597,plain,(
    ! [A_289] :
      ( r2_hidden('#skF_1'(A_289,'#skF_5'),'#skF_5')
      | A_289 = '#skF_5'
      | '#skF_2'(A_289,'#skF_5') = '#skF_5'
      | ~ r2_hidden('#skF_2'(A_289,'#skF_5'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2062,c_2641])).

tff(c_6624,plain,
    ( '#skF_2'('#skF_4','#skF_5') = '#skF_5'
    | r2_hidden('#skF_1'('#skF_4','#skF_5'),'#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_8,c_6597])).

tff(c_6648,plain,
    ( '#skF_2'('#skF_4','#skF_5') = '#skF_5'
    | r2_hidden('#skF_1'('#skF_4','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_1972,c_1972,c_6624])).

tff(c_6719,plain,(
    r2_hidden('#skF_1'('#skF_4','#skF_5'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_6648])).

tff(c_6743,plain,(
    r2_hidden('#skF_1'('#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_6719,c_1994])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r2_hidden('#skF_2'(A_1,B_2),A_1)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),A_1)
      | ~ r2_hidden('#skF_2'(A_1,B_2),B_2)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_6824,plain,
    ( ~ r2_hidden('#skF_2'('#skF_4','#skF_5'),'#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6743,c_2])).

tff(c_6848,plain,(
    ~ r2_hidden('#skF_2'('#skF_4','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_1972,c_6824])).

tff(c_6873,plain,
    ( '#skF_2'('#skF_4','#skF_5') = '#skF_5'
    | ~ r2_hidden('#skF_2'('#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_2062,c_6848])).

tff(c_6874,plain,(
    ~ r2_hidden('#skF_2'('#skF_4','#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_6873])).

tff(c_6890,plain,
    ( ~ r2_hidden('#skF_1'('#skF_4','#skF_5'),'#skF_4')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6,c_6874])).

tff(c_6906,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6743,c_6890])).

tff(c_6908,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1972,c_6906])).

tff(c_6909,plain,(
    '#skF_2'('#skF_4','#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_6873])).

tff(c_6911,plain,(
    ~ r2_hidden('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6909,c_6848])).

tff(c_6915,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3024,c_6911])).

tff(c_6917,plain,(
    ~ r2_hidden('#skF_1'('#skF_4','#skF_5'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_6648])).

tff(c_6916,plain,(
    '#skF_2'('#skF_4','#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_6648])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2),B_2)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_6929,plain,
    ( r2_hidden('#skF_1'('#skF_4','#skF_5'),'#skF_5')
    | ~ r2_hidden('#skF_5','#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_6916,c_4])).

tff(c_6945,plain,
    ( r2_hidden('#skF_1'('#skF_4','#skF_5'),'#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3024,c_6929])).

tff(c_6946,plain,(
    r2_hidden('#skF_1'('#skF_4','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_1972,c_6945])).

tff(c_7046,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6917,c_6946])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:26:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.40/2.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.40/2.29  
% 6.40/2.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.66/2.30  %$ r2_hidden > r1_ordinal1 > v4_ordinal1 > v3_ordinal1 > v1_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 6.66/2.30  
% 6.66/2.30  %Foreground sorts:
% 6.66/2.30  
% 6.66/2.30  
% 6.66/2.30  %Background operators:
% 6.66/2.30  
% 6.66/2.30  
% 6.66/2.30  %Foreground operators:
% 6.66/2.30  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 6.66/2.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.66/2.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.66/2.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.66/2.30  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 6.66/2.30  tff('#skF_5', type, '#skF_5': $i).
% 6.66/2.30  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 6.66/2.30  tff(v4_ordinal1, type, v4_ordinal1: $i > $o).
% 6.66/2.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.66/2.30  tff('#skF_4', type, '#skF_4': $i).
% 6.66/2.30  tff('#skF_3', type, '#skF_3': $i > $i).
% 6.66/2.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.66/2.30  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.66/2.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.66/2.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.66/2.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.66/2.30  
% 6.66/2.32  tff(f_106, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (~(~v4_ordinal1(A) & (![B]: (v3_ordinal1(B) => ~(A = k1_ordinal1(B))))) & ~((?[B]: (v3_ordinal1(B) & (A = k1_ordinal1(B)))) & v4_ordinal1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_ordinal1)).
% 6.66/2.32  tff(f_85, axiom, (![A]: (v3_ordinal1(A) => (v4_ordinal1(A) <=> (![B]: (v3_ordinal1(B) => (r2_hidden(B, A) => r2_hidden(k1_ordinal1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_ordinal1)).
% 6.66/2.32  tff(f_41, axiom, (![A]: (v3_ordinal1(A) => (~v1_xboole_0(k1_ordinal1(A)) & v3_ordinal1(k1_ordinal1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_ordinal1)).
% 6.66/2.32  tff(f_65, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) <=> r1_ordinal1(k1_ordinal1(A), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_ordinal1)).
% 6.66/2.32  tff(f_74, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_ordinal1)).
% 6.66/2.32  tff(f_47, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_ordinal1)).
% 6.66/2.32  tff(f_50, axiom, (![A]: ~(A = k1_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_ordinal1)).
% 6.66/2.32  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 6.66/2.32  tff(c_42, plain, (v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.66/2.32  tff(c_40, plain, (![A_17]: (v3_ordinal1('#skF_3'(A_17)) | v4_ordinal1(A_17) | ~v3_ordinal1(A_17))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.66/2.32  tff(c_38, plain, (![A_17]: (r2_hidden('#skF_3'(A_17), A_17) | v4_ordinal1(A_17) | ~v3_ordinal1(A_17))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.66/2.32  tff(c_12, plain, (![A_5]: (v3_ordinal1(k1_ordinal1(A_5)) | ~v3_ordinal1(A_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.66/2.32  tff(c_28, plain, (![A_11, B_13]: (r1_ordinal1(k1_ordinal1(A_11), B_13) | ~r2_hidden(A_11, B_13) | ~v3_ordinal1(B_13) | ~v3_ordinal1(A_11))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.66/2.32  tff(c_131, plain, (![A_44, B_45]: (r2_hidden(A_44, k1_ordinal1(B_45)) | ~r1_ordinal1(A_44, B_45) | ~v3_ordinal1(B_45) | ~v3_ordinal1(A_44))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.66/2.32  tff(c_16, plain, (![B_7, A_6]: (B_7=A_6 | r2_hidden(A_6, B_7) | ~r2_hidden(A_6, k1_ordinal1(B_7)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.66/2.32  tff(c_329, plain, (![B_68, A_69]: (B_68=A_69 | r2_hidden(A_69, B_68) | ~r1_ordinal1(A_69, B_68) | ~v3_ordinal1(B_68) | ~v3_ordinal1(A_69))), inference(resolution, [status(thm)], [c_131, c_16])).
% 6.66/2.32  tff(c_36, plain, (![A_17]: (~r2_hidden(k1_ordinal1('#skF_3'(A_17)), A_17) | v4_ordinal1(A_17) | ~v3_ordinal1(A_17))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.66/2.32  tff(c_806, plain, (![B_111]: (v4_ordinal1(B_111) | k1_ordinal1('#skF_3'(B_111))=B_111 | ~r1_ordinal1(k1_ordinal1('#skF_3'(B_111)), B_111) | ~v3_ordinal1(B_111) | ~v3_ordinal1(k1_ordinal1('#skF_3'(B_111))))), inference(resolution, [status(thm)], [c_329, c_36])).
% 6.66/2.32  tff(c_1583, plain, (![B_149]: (v4_ordinal1(B_149) | k1_ordinal1('#skF_3'(B_149))=B_149 | ~v3_ordinal1(k1_ordinal1('#skF_3'(B_149))) | ~r2_hidden('#skF_3'(B_149), B_149) | ~v3_ordinal1(B_149) | ~v3_ordinal1('#skF_3'(B_149)))), inference(resolution, [status(thm)], [c_28, c_806])).
% 6.66/2.32  tff(c_1588, plain, (![B_150]: (v4_ordinal1(B_150) | k1_ordinal1('#skF_3'(B_150))=B_150 | ~r2_hidden('#skF_3'(B_150), B_150) | ~v3_ordinal1(B_150) | ~v3_ordinal1('#skF_3'(B_150)))), inference(resolution, [status(thm)], [c_12, c_1583])).
% 6.66/2.32  tff(c_1618, plain, (![A_151]: (k1_ordinal1('#skF_3'(A_151))=A_151 | ~v3_ordinal1('#skF_3'(A_151)) | v4_ordinal1(A_151) | ~v3_ordinal1(A_151))), inference(resolution, [status(thm)], [c_38, c_1588])).
% 6.66/2.32  tff(c_1623, plain, (![A_152]: (k1_ordinal1('#skF_3'(A_152))=A_152 | v4_ordinal1(A_152) | ~v3_ordinal1(A_152))), inference(resolution, [status(thm)], [c_40, c_1618])).
% 6.66/2.32  tff(c_80, plain, (![A_31]: (v3_ordinal1('#skF_3'(A_31)) | v4_ordinal1(A_31) | ~v3_ordinal1(A_31))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.66/2.32  tff(c_54, plain, (~v4_ordinal1('#skF_4') | v3_ordinal1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.66/2.32  tff(c_57, plain, (~v4_ordinal1('#skF_4')), inference(splitLeft, [status(thm)], [c_54])).
% 6.66/2.32  tff(c_44, plain, (![B_23]: (k1_ordinal1(B_23)!='#skF_4' | ~v3_ordinal1(B_23) | v4_ordinal1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.66/2.32  tff(c_69, plain, (![B_23]: (k1_ordinal1(B_23)!='#skF_4' | ~v3_ordinal1(B_23))), inference(negUnitSimplification, [status(thm)], [c_57, c_44])).
% 6.66/2.32  tff(c_84, plain, (![A_31]: (k1_ordinal1('#skF_3'(A_31))!='#skF_4' | v4_ordinal1(A_31) | ~v3_ordinal1(A_31))), inference(resolution, [status(thm)], [c_80, c_69])).
% 6.66/2.32  tff(c_1806, plain, (![A_152]: (A_152!='#skF_4' | v4_ordinal1(A_152) | ~v3_ordinal1(A_152) | v4_ordinal1(A_152) | ~v3_ordinal1(A_152))), inference(superposition, [status(thm), theory('equality')], [c_1623, c_84])).
% 6.66/2.32  tff(c_1946, plain, (![A_159]: (A_159!='#skF_4' | ~v3_ordinal1(A_159) | v4_ordinal1(A_159))), inference(factorization, [status(thm), theory('equality')], [c_1806])).
% 6.66/2.32  tff(c_1949, plain, (~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_1946, c_57])).
% 6.66/2.32  tff(c_1953, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_1949])).
% 6.66/2.32  tff(c_1954, plain, (v3_ordinal1('#skF_5')), inference(splitRight, [status(thm)], [c_54])).
% 6.66/2.32  tff(c_1955, plain, (v4_ordinal1('#skF_4')), inference(splitRight, [status(thm)], [c_54])).
% 6.66/2.32  tff(c_50, plain, (~v4_ordinal1('#skF_4') | k1_ordinal1('#skF_5')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.66/2.32  tff(c_1959, plain, (k1_ordinal1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1955, c_50])).
% 6.66/2.32  tff(c_18, plain, (![B_7]: (r2_hidden(B_7, k1_ordinal1(B_7)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.66/2.32  tff(c_1969, plain, (r2_hidden('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1959, c_18])).
% 6.66/2.32  tff(c_2203, plain, (![A_186, B_187]: (r1_ordinal1(A_186, B_187) | ~r2_hidden(A_186, k1_ordinal1(B_187)) | ~v3_ordinal1(B_187) | ~v3_ordinal1(A_186))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.66/2.32  tff(c_2216, plain, (![A_186]: (r1_ordinal1(A_186, '#skF_5') | ~r2_hidden(A_186, '#skF_4') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1(A_186))), inference(superposition, [status(thm), theory('equality')], [c_1959, c_2203])).
% 6.66/2.32  tff(c_2227, plain, (![A_189]: (r1_ordinal1(A_189, '#skF_5') | ~r2_hidden(A_189, '#skF_4') | ~v3_ordinal1(A_189))), inference(demodulation, [status(thm), theory('equality')], [c_1954, c_2216])).
% 6.66/2.32  tff(c_2237, plain, (r1_ordinal1('#skF_5', '#skF_5') | ~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_1969, c_2227])).
% 6.66/2.32  tff(c_2244, plain, (r1_ordinal1('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1954, c_2237])).
% 6.66/2.32  tff(c_2152, plain, (![A_183, B_184]: (r2_hidden(A_183, k1_ordinal1(B_184)) | ~r1_ordinal1(A_183, B_184) | ~v3_ordinal1(B_184) | ~v3_ordinal1(A_183))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.66/2.32  tff(c_2169, plain, (![A_183]: (r2_hidden(A_183, '#skF_4') | ~r1_ordinal1(A_183, '#skF_5') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1(A_183))), inference(superposition, [status(thm), theory('equality')], [c_1959, c_2152])).
% 6.66/2.32  tff(c_2177, plain, (![A_183]: (r2_hidden(A_183, '#skF_4') | ~r1_ordinal1(A_183, '#skF_5') | ~v3_ordinal1(A_183))), inference(demodulation, [status(thm), theory('equality')], [c_1954, c_2169])).
% 6.66/2.32  tff(c_2826, plain, (![B_215, A_216]: (r2_hidden(k1_ordinal1(B_215), A_216) | ~r2_hidden(B_215, A_216) | ~v3_ordinal1(B_215) | ~v4_ordinal1(A_216) | ~v3_ordinal1(A_216))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.66/2.32  tff(c_2863, plain, (![A_216]: (r2_hidden('#skF_4', A_216) | ~r2_hidden('#skF_5', A_216) | ~v3_ordinal1('#skF_5') | ~v4_ordinal1(A_216) | ~v3_ordinal1(A_216))), inference(superposition, [status(thm), theory('equality')], [c_1959, c_2826])).
% 6.66/2.32  tff(c_2937, plain, (![A_218]: (r2_hidden('#skF_4', A_218) | ~r2_hidden('#skF_5', A_218) | ~v4_ordinal1(A_218) | ~v3_ordinal1(A_218))), inference(demodulation, [status(thm), theory('equality')], [c_1954, c_2863])).
% 6.66/2.32  tff(c_2948, plain, (r2_hidden('#skF_4', '#skF_4') | ~v4_ordinal1('#skF_4') | ~v3_ordinal1('#skF_4') | ~r1_ordinal1('#skF_5', '#skF_5') | ~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_2177, c_2937])).
% 6.66/2.32  tff(c_2974, plain, (r2_hidden('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1954, c_2244, c_42, c_1955, c_2948])).
% 6.66/2.32  tff(c_2224, plain, (![A_186]: (r1_ordinal1(A_186, '#skF_5') | ~r2_hidden(A_186, '#skF_4') | ~v3_ordinal1(A_186))), inference(demodulation, [status(thm), theory('equality')], [c_1954, c_2216])).
% 6.66/2.32  tff(c_2994, plain, (r1_ordinal1('#skF_4', '#skF_5') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_2974, c_2224])).
% 6.66/2.32  tff(c_3006, plain, (r1_ordinal1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2994])).
% 6.66/2.32  tff(c_2313, plain, (![A_195, B_196]: (r2_hidden(A_195, B_196) | ~r1_ordinal1(k1_ordinal1(A_195), B_196) | ~v3_ordinal1(B_196) | ~v3_ordinal1(A_195))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.66/2.32  tff(c_2327, plain, (![B_196]: (r2_hidden('#skF_5', B_196) | ~r1_ordinal1('#skF_4', B_196) | ~v3_ordinal1(B_196) | ~v3_ordinal1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1959, c_2313])).
% 6.66/2.32  tff(c_2333, plain, (![B_196]: (r2_hidden('#skF_5', B_196) | ~r1_ordinal1('#skF_4', B_196) | ~v3_ordinal1(B_196))), inference(demodulation, [status(thm), theory('equality')], [c_1954, c_2327])).
% 6.66/2.32  tff(c_2023, plain, (![A_170]: (r2_hidden('#skF_3'(A_170), A_170) | v4_ordinal1(A_170) | ~v3_ordinal1(A_170))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.66/2.32  tff(c_1991, plain, (![A_164, B_165]: (~r2_hidden(A_164, B_165) | r2_hidden(A_164, k1_ordinal1(B_165)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.66/2.32  tff(c_1994, plain, (![A_164]: (~r2_hidden(A_164, '#skF_5') | r2_hidden(A_164, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1959, c_1991])).
% 6.66/2.32  tff(c_2030, plain, (r2_hidden('#skF_3'('#skF_5'), '#skF_4') | v4_ordinal1('#skF_5') | ~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_2023, c_1994])).
% 6.66/2.32  tff(c_2034, plain, (r2_hidden('#skF_3'('#skF_5'), '#skF_4') | v4_ordinal1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1954, c_2030])).
% 6.66/2.32  tff(c_2035, plain, (v4_ordinal1('#skF_5')), inference(splitLeft, [status(thm)], [c_2034])).
% 6.66/2.32  tff(c_2860, plain, (![B_215]: (r2_hidden(k1_ordinal1(B_215), '#skF_4') | ~r2_hidden(B_215, '#skF_5') | ~v3_ordinal1(B_215) | ~v4_ordinal1('#skF_5') | ~v3_ordinal1('#skF_5'))), inference(resolution, [status(thm)], [c_2826, c_1994])).
% 6.66/2.32  tff(c_2883, plain, (![B_217]: (r2_hidden(k1_ordinal1(B_217), '#skF_4') | ~r2_hidden(B_217, '#skF_5') | ~v3_ordinal1(B_217))), inference(demodulation, [status(thm), theory('equality')], [c_1954, c_2035, c_2860])).
% 6.66/2.32  tff(c_2902, plain, (r2_hidden('#skF_4', '#skF_4') | ~r2_hidden('#skF_5', '#skF_5') | ~v3_ordinal1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1959, c_2883])).
% 6.66/2.32  tff(c_2915, plain, (r2_hidden('#skF_4', '#skF_4') | ~r2_hidden('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1954, c_2902])).
% 6.66/2.32  tff(c_2916, plain, (~r2_hidden('#skF_5', '#skF_5')), inference(splitLeft, [status(thm)], [c_2915])).
% 6.66/2.32  tff(c_2922, plain, (~r1_ordinal1('#skF_4', '#skF_5') | ~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_2333, c_2916])).
% 6.66/2.32  tff(c_2932, plain, (~r1_ordinal1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1954, c_2922])).
% 6.66/2.32  tff(c_3022, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3006, c_2932])).
% 6.66/2.32  tff(c_3024, plain, (r2_hidden('#skF_5', '#skF_5')), inference(splitRight, [status(thm)], [c_2915])).
% 6.66/2.32  tff(c_22, plain, (![A_8]: (k1_ordinal1(A_8)!=A_8)), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.66/2.32  tff(c_1972, plain, ('#skF_5'!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1959, c_22])).
% 6.66/2.32  tff(c_8, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r2_hidden('#skF_2'(A_1, B_2), A_1) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.66/2.32  tff(c_2052, plain, (![B_174, A_175]: (B_174=A_175 | r2_hidden(A_175, B_174) | ~r2_hidden(A_175, k1_ordinal1(B_174)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.66/2.32  tff(c_2062, plain, (![A_175]: (A_175='#skF_5' | r2_hidden(A_175, '#skF_5') | ~r2_hidden(A_175, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1959, c_2052])).
% 6.66/2.32  tff(c_2641, plain, (![A_209, B_210]: (r2_hidden('#skF_1'(A_209, B_210), B_210) | ~r2_hidden('#skF_2'(A_209, B_210), B_210) | B_210=A_209)), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.66/2.32  tff(c_6597, plain, (![A_289]: (r2_hidden('#skF_1'(A_289, '#skF_5'), '#skF_5') | A_289='#skF_5' | '#skF_2'(A_289, '#skF_5')='#skF_5' | ~r2_hidden('#skF_2'(A_289, '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_2062, c_2641])).
% 6.66/2.32  tff(c_6624, plain, ('#skF_2'('#skF_4', '#skF_5')='#skF_5' | r2_hidden('#skF_1'('#skF_4', '#skF_5'), '#skF_5') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_8, c_6597])).
% 6.66/2.32  tff(c_6648, plain, ('#skF_2'('#skF_4', '#skF_5')='#skF_5' | r2_hidden('#skF_1'('#skF_4', '#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_1972, c_1972, c_6624])).
% 6.66/2.32  tff(c_6719, plain, (r2_hidden('#skF_1'('#skF_4', '#skF_5'), '#skF_5')), inference(splitLeft, [status(thm)], [c_6648])).
% 6.66/2.32  tff(c_6743, plain, (r2_hidden('#skF_1'('#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_6719, c_1994])).
% 6.66/2.32  tff(c_6, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), A_1) | r2_hidden('#skF_2'(A_1, B_2), A_1) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.66/2.32  tff(c_2, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), A_1) | ~r2_hidden('#skF_2'(A_1, B_2), B_2) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.66/2.32  tff(c_6824, plain, (~r2_hidden('#skF_2'('#skF_4', '#skF_5'), '#skF_5') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_6743, c_2])).
% 6.66/2.32  tff(c_6848, plain, (~r2_hidden('#skF_2'('#skF_4', '#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_1972, c_6824])).
% 6.66/2.32  tff(c_6873, plain, ('#skF_2'('#skF_4', '#skF_5')='#skF_5' | ~r2_hidden('#skF_2'('#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_2062, c_6848])).
% 6.66/2.32  tff(c_6874, plain, (~r2_hidden('#skF_2'('#skF_4', '#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_6873])).
% 6.66/2.32  tff(c_6890, plain, (~r2_hidden('#skF_1'('#skF_4', '#skF_5'), '#skF_4') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_6, c_6874])).
% 6.66/2.32  tff(c_6906, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6743, c_6890])).
% 6.66/2.32  tff(c_6908, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1972, c_6906])).
% 6.66/2.32  tff(c_6909, plain, ('#skF_2'('#skF_4', '#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_6873])).
% 6.66/2.32  tff(c_6911, plain, (~r2_hidden('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6909, c_6848])).
% 6.66/2.32  tff(c_6915, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3024, c_6911])).
% 6.66/2.32  tff(c_6917, plain, (~r2_hidden('#skF_1'('#skF_4', '#skF_5'), '#skF_5')), inference(splitRight, [status(thm)], [c_6648])).
% 6.66/2.32  tff(c_6916, plain, ('#skF_2'('#skF_4', '#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_6648])).
% 6.66/2.32  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | ~r2_hidden('#skF_2'(A_1, B_2), B_2) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.66/2.32  tff(c_6929, plain, (r2_hidden('#skF_1'('#skF_4', '#skF_5'), '#skF_5') | ~r2_hidden('#skF_5', '#skF_5') | '#skF_5'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_6916, c_4])).
% 6.66/2.32  tff(c_6945, plain, (r2_hidden('#skF_1'('#skF_4', '#skF_5'), '#skF_5') | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3024, c_6929])).
% 6.66/2.32  tff(c_6946, plain, (r2_hidden('#skF_1'('#skF_4', '#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_1972, c_6945])).
% 6.66/2.32  tff(c_7046, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6917, c_6946])).
% 6.66/2.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.66/2.32  
% 6.66/2.32  Inference rules
% 6.66/2.32  ----------------------
% 6.66/2.32  #Ref     : 0
% 6.66/2.32  #Sup     : 1260
% 6.66/2.32  #Fact    : 2
% 6.66/2.32  #Define  : 0
% 6.66/2.32  #Split   : 13
% 6.66/2.32  #Chain   : 0
% 6.66/2.32  #Close   : 0
% 6.66/2.32  
% 6.66/2.32  Ordering : KBO
% 6.66/2.32  
% 6.66/2.32  Simplification rules
% 6.66/2.32  ----------------------
% 6.66/2.32  #Subsume      : 156
% 6.66/2.32  #Demod        : 1165
% 6.66/2.32  #Tautology    : 450
% 6.66/2.32  #SimpNegUnit  : 111
% 6.66/2.32  #BackRed      : 7
% 6.66/2.32  
% 6.66/2.32  #Partial instantiations: 0
% 6.66/2.32  #Strategies tried      : 1
% 6.66/2.32  
% 6.66/2.32  Timing (in seconds)
% 6.66/2.32  ----------------------
% 6.66/2.32  Preprocessing        : 0.28
% 6.66/2.32  Parsing              : 0.15
% 6.66/2.32  CNF conversion       : 0.02
% 6.66/2.32  Main loop            : 1.24
% 6.66/2.32  Inferencing          : 0.43
% 6.66/2.32  Reduction            : 0.34
% 6.66/2.32  Demodulation         : 0.21
% 6.66/2.32  BG Simplification    : 0.05
% 6.66/2.32  Subsumption          : 0.35
% 6.66/2.32  Abstraction          : 0.05
% 6.66/2.32  MUC search           : 0.00
% 6.66/2.32  Cooper               : 0.00
% 6.66/2.32  Total                : 1.57
% 6.66/2.32  Index Insertion      : 0.00
% 6.66/2.32  Index Deletion       : 0.00
% 6.66/2.32  Index Matching       : 0.00
% 6.66/2.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
