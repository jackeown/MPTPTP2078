%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:51 EST 2020

% Result     : Theorem 5.70s
% Output     : CNFRefutation 6.06s
% Verified   : 
% Statistics : Number of formulae       :  166 (1071 expanded)
%              Number of leaves         :   31 ( 415 expanded)
%              Depth                    :   20
%              Number of atoms          :  582 (7016 expanded)
%              Number of equality atoms :   57 ( 365 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > m1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_orders_2,type,(
    k3_orders_2: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(m1_orders_2,type,(
    m1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_164,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                   => ! [E] :
                        ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(A)))
                       => ( ( r2_orders_2(A,B,C)
                            & r2_hidden(B,D)
                            & r2_hidden(C,E)
                            & m1_orders_2(E,A,D) )
                         => r2_hidden(B,E) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_orders_2)).

tff(f_80,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( B != k1_xboole_0
                 => ( m1_orders_2(C,A,B)
                  <=> ? [D] :
                        ( m1_subset_1(D,u1_struct_0(A))
                        & r2_hidden(D,B)
                        & C = k3_orders_2(A,B,D) ) ) )
                & ( B = k1_xboole_0
                 => ( m1_orders_2(C,A,B)
                  <=> C = k1_xboole_0 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_orders_2)).

tff(f_106,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                 => ( r2_hidden(B,k3_orders_2(A,D,C))
                  <=> ( r2_orders_2(A,B,C)
                      & r2_hidden(B,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).

tff(f_130,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                 => ( r2_orders_2(A,B,C)
                   => r1_tarski(k3_orders_2(A,D,B),k3_orders_2(A,D,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_orders_2)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_72,plain,(
    ! [A_95,B_96] :
      ( r2_hidden('#skF_1'(A_95,B_96),A_95)
      | r1_tarski(A_95,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_80,plain,(
    ! [A_95] : r1_tarski(A_95,A_95) ),
    inference(resolution,[status(thm)],[c_72,c_4])).

tff(c_34,plain,(
    ~ r2_hidden('#skF_4','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_42,plain,(
    r2_orders_2('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_40,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_36,plain,(
    m1_orders_2('#skF_7','#skF_3','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_46,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_58,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_56,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_54,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_52,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_44,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_2208,plain,(
    ! [A_329,B_330,C_331] :
      ( r2_hidden('#skF_2'(A_329,B_330,C_331),B_330)
      | ~ m1_orders_2(C_331,A_329,B_330)
      | k1_xboole_0 = B_330
      | ~ m1_subset_1(C_331,k1_zfmisc_1(u1_struct_0(A_329)))
      | ~ m1_subset_1(B_330,k1_zfmisc_1(u1_struct_0(A_329)))
      | ~ l1_orders_2(A_329)
      | ~ v5_orders_2(A_329)
      | ~ v4_orders_2(A_329)
      | ~ v3_orders_2(A_329)
      | v2_struct_0(A_329) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2212,plain,(
    ! [B_330] :
      ( r2_hidden('#skF_2'('#skF_3',B_330,'#skF_7'),B_330)
      | ~ m1_orders_2('#skF_7','#skF_3',B_330)
      | k1_xboole_0 = B_330
      | ~ m1_subset_1(B_330,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_44,c_2208])).

tff(c_2221,plain,(
    ! [B_330] :
      ( r2_hidden('#skF_2'('#skF_3',B_330,'#skF_7'),B_330)
      | ~ m1_orders_2('#skF_7','#skF_3',B_330)
      | k1_xboole_0 = B_330
      | ~ m1_subset_1(B_330,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_2212])).

tff(c_2227,plain,(
    ! [B_332] :
      ( r2_hidden('#skF_2'('#skF_3',B_332,'#skF_7'),B_332)
      | ~ m1_orders_2('#skF_7','#skF_3',B_332)
      | k1_xboole_0 = B_332
      | ~ m1_subset_1(B_332,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2221])).

tff(c_2233,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_6','#skF_7'),'#skF_6')
    | ~ m1_orders_2('#skF_7','#skF_3','#skF_6')
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_46,c_2227])).

tff(c_2238,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_6','#skF_7'),'#skF_6')
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2233])).

tff(c_2239,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_2238])).

tff(c_218,plain,(
    ! [A_131,B_132,C_133] :
      ( r2_hidden('#skF_2'(A_131,B_132,C_133),B_132)
      | ~ m1_orders_2(C_133,A_131,B_132)
      | k1_xboole_0 = B_132
      | ~ m1_subset_1(C_133,k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ m1_subset_1(B_132,k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ l1_orders_2(A_131)
      | ~ v5_orders_2(A_131)
      | ~ v4_orders_2(A_131)
      | ~ v3_orders_2(A_131)
      | v2_struct_0(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_220,plain,(
    ! [B_132] :
      ( r2_hidden('#skF_2'('#skF_3',B_132,'#skF_7'),B_132)
      | ~ m1_orders_2('#skF_7','#skF_3',B_132)
      | k1_xboole_0 = B_132
      | ~ m1_subset_1(B_132,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_44,c_218])).

tff(c_225,plain,(
    ! [B_132] :
      ( r2_hidden('#skF_2'('#skF_3',B_132,'#skF_7'),B_132)
      | ~ m1_orders_2('#skF_7','#skF_3',B_132)
      | k1_xboole_0 = B_132
      | ~ m1_subset_1(B_132,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_220])).

tff(c_248,plain,(
    ! [B_138] :
      ( r2_hidden('#skF_2'('#skF_3',B_138,'#skF_7'),B_138)
      | ~ m1_orders_2('#skF_7','#skF_3',B_138)
      | k1_xboole_0 = B_138
      | ~ m1_subset_1(B_138,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_225])).

tff(c_252,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_6','#skF_7'),'#skF_6')
    | ~ m1_orders_2('#skF_7','#skF_3','#skF_6')
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_46,c_248])).

tff(c_256,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_6','#skF_7'),'#skF_6')
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_252])).

tff(c_257,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_256])).

tff(c_197,plain,(
    ! [C_125,A_126] :
      ( k1_xboole_0 = C_125
      | ~ m1_orders_2(C_125,A_126,k1_xboole_0)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ l1_orders_2(A_126)
      | ~ v5_orders_2(A_126)
      | ~ v4_orders_2(A_126)
      | ~ v3_orders_2(A_126)
      | v2_struct_0(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_199,plain,
    ( k1_xboole_0 = '#skF_7'
    | ~ m1_orders_2('#skF_7','#skF_3',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_197])).

tff(c_204,plain,
    ( k1_xboole_0 = '#skF_7'
    | ~ m1_orders_2('#skF_7','#skF_3',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_199])).

tff(c_205,plain,
    ( k1_xboole_0 = '#skF_7'
    | ~ m1_orders_2('#skF_7','#skF_3',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_204])).

tff(c_210,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_205])).

tff(c_260,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_210])).

tff(c_269,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_260])).

tff(c_271,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_256])).

tff(c_24,plain,(
    ! [A_12,B_24,C_30] :
      ( m1_subset_1('#skF_2'(A_12,B_24,C_30),u1_struct_0(A_12))
      | ~ m1_orders_2(C_30,A_12,B_24)
      | k1_xboole_0 = B_24
      | ~ m1_subset_1(C_30,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ l1_orders_2(A_12)
      | ~ v5_orders_2(A_12)
      | ~ v4_orders_2(A_12)
      | ~ v3_orders_2(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_615,plain,(
    ! [A_203,B_204,C_205] :
      ( k3_orders_2(A_203,B_204,'#skF_2'(A_203,B_204,C_205)) = C_205
      | ~ m1_orders_2(C_205,A_203,B_204)
      | k1_xboole_0 = B_204
      | ~ m1_subset_1(C_205,k1_zfmisc_1(u1_struct_0(A_203)))
      | ~ m1_subset_1(B_204,k1_zfmisc_1(u1_struct_0(A_203)))
      | ~ l1_orders_2(A_203)
      | ~ v5_orders_2(A_203)
      | ~ v4_orders_2(A_203)
      | ~ v3_orders_2(A_203)
      | v2_struct_0(A_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_617,plain,(
    ! [B_204] :
      ( k3_orders_2('#skF_3',B_204,'#skF_2'('#skF_3',B_204,'#skF_7')) = '#skF_7'
      | ~ m1_orders_2('#skF_7','#skF_3',B_204)
      | k1_xboole_0 = B_204
      | ~ m1_subset_1(B_204,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_44,c_615])).

tff(c_622,plain,(
    ! [B_204] :
      ( k3_orders_2('#skF_3',B_204,'#skF_2'('#skF_3',B_204,'#skF_7')) = '#skF_7'
      | ~ m1_orders_2('#skF_7','#skF_3',B_204)
      | k1_xboole_0 = B_204
      | ~ m1_subset_1(B_204,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_617])).

tff(c_641,plain,(
    ! [B_210] :
      ( k3_orders_2('#skF_3',B_210,'#skF_2'('#skF_3',B_210,'#skF_7')) = '#skF_7'
      | ~ m1_orders_2('#skF_7','#skF_3',B_210)
      | k1_xboole_0 = B_210
      | ~ m1_subset_1(B_210,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_622])).

tff(c_645,plain,
    ( k3_orders_2('#skF_3','#skF_6','#skF_2'('#skF_3','#skF_6','#skF_7')) = '#skF_7'
    | ~ m1_orders_2('#skF_7','#skF_3','#skF_6')
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_46,c_641])).

tff(c_649,plain,
    ( k3_orders_2('#skF_3','#skF_6','#skF_2'('#skF_3','#skF_6','#skF_7')) = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_645])).

tff(c_650,plain,(
    k3_orders_2('#skF_3','#skF_6','#skF_2'('#skF_3','#skF_6','#skF_7')) = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_271,c_649])).

tff(c_28,plain,(
    ! [B_42,D_48,A_34,C_46] :
      ( r2_hidden(B_42,D_48)
      | ~ r2_hidden(B_42,k3_orders_2(A_34,D_48,C_46))
      | ~ m1_subset_1(D_48,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ m1_subset_1(C_46,u1_struct_0(A_34))
      | ~ m1_subset_1(B_42,u1_struct_0(A_34))
      | ~ l1_orders_2(A_34)
      | ~ v5_orders_2(A_34)
      | ~ v4_orders_2(A_34)
      | ~ v3_orders_2(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_664,plain,(
    ! [B_42] :
      ( r2_hidden(B_42,'#skF_6')
      | ~ r2_hidden(B_42,'#skF_7')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_6','#skF_7'),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_42,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_650,c_28])).

tff(c_673,plain,(
    ! [B_42] :
      ( r2_hidden(B_42,'#skF_6')
      | ~ r2_hidden(B_42,'#skF_7')
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_6','#skF_7'),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_42,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_46,c_664])).

tff(c_674,plain,(
    ! [B_42] :
      ( r2_hidden(B_42,'#skF_6')
      | ~ r2_hidden(B_42,'#skF_7')
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_6','#skF_7'),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_42,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_673])).

tff(c_677,plain,(
    ~ m1_subset_1('#skF_2'('#skF_3','#skF_6','#skF_7'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_674])).

tff(c_680,plain,
    ( ~ m1_orders_2('#skF_7','#skF_3','#skF_6')
    | k1_xboole_0 = '#skF_6'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_677])).

tff(c_689,plain,
    ( k1_xboole_0 = '#skF_6'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_46,c_44,c_36,c_680])).

tff(c_691,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_271,c_689])).

tff(c_693,plain,(
    m1_subset_1('#skF_2'('#skF_3','#skF_6','#skF_7'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_674])).

tff(c_38,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_90,plain,(
    ! [C_100,B_101,A_102] :
      ( r2_hidden(C_100,B_101)
      | ~ r2_hidden(C_100,A_102)
      | ~ r1_tarski(A_102,B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_98,plain,(
    ! [B_101] :
      ( r2_hidden('#skF_5',B_101)
      | ~ r1_tarski('#skF_7',B_101) ) ),
    inference(resolution,[status(thm)],[c_38,c_90])).

tff(c_534,plain,(
    ! [A_183,B_184,C_185,D_186] :
      ( r2_orders_2(A_183,B_184,C_185)
      | ~ r2_hidden(B_184,k3_orders_2(A_183,D_186,C_185))
      | ~ m1_subset_1(D_186,k1_zfmisc_1(u1_struct_0(A_183)))
      | ~ m1_subset_1(C_185,u1_struct_0(A_183))
      | ~ m1_subset_1(B_184,u1_struct_0(A_183))
      | ~ l1_orders_2(A_183)
      | ~ v5_orders_2(A_183)
      | ~ v4_orders_2(A_183)
      | ~ v3_orders_2(A_183)
      | v2_struct_0(A_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_586,plain,(
    ! [A_194,C_195,D_196] :
      ( r2_orders_2(A_194,'#skF_5',C_195)
      | ~ m1_subset_1(D_196,k1_zfmisc_1(u1_struct_0(A_194)))
      | ~ m1_subset_1(C_195,u1_struct_0(A_194))
      | ~ m1_subset_1('#skF_5',u1_struct_0(A_194))
      | ~ l1_orders_2(A_194)
      | ~ v5_orders_2(A_194)
      | ~ v4_orders_2(A_194)
      | ~ v3_orders_2(A_194)
      | v2_struct_0(A_194)
      | ~ r1_tarski('#skF_7',k3_orders_2(A_194,D_196,C_195)) ) ),
    inference(resolution,[status(thm)],[c_98,c_534])).

tff(c_590,plain,(
    ! [C_195] :
      ( r2_orders_2('#skF_3','#skF_5',C_195)
      | ~ m1_subset_1(C_195,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_tarski('#skF_7',k3_orders_2('#skF_3','#skF_6',C_195)) ) ),
    inference(resolution,[status(thm)],[c_46,c_586])).

tff(c_597,plain,(
    ! [C_195] :
      ( r2_orders_2('#skF_3','#skF_5',C_195)
      | ~ m1_subset_1(C_195,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3')
      | ~ r1_tarski('#skF_7',k3_orders_2('#skF_3','#skF_6',C_195)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_48,c_590])).

tff(c_598,plain,(
    ! [C_195] :
      ( r2_orders_2('#skF_3','#skF_5',C_195)
      | ~ m1_subset_1(C_195,u1_struct_0('#skF_3'))
      | ~ r1_tarski('#skF_7',k3_orders_2('#skF_3','#skF_6',C_195)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_597])).

tff(c_657,plain,
    ( r2_orders_2('#skF_3','#skF_5','#skF_2'('#skF_3','#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_6','#skF_7'),u1_struct_0('#skF_3'))
    | ~ r1_tarski('#skF_7','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_650,c_598])).

tff(c_668,plain,
    ( r2_orders_2('#skF_3','#skF_5','#skF_2'('#skF_3','#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_6','#skF_7'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_657])).

tff(c_676,plain,(
    ~ m1_subset_1('#skF_2'('#skF_3','#skF_6','#skF_7'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_668])).

tff(c_695,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_693,c_676])).

tff(c_696,plain,(
    r2_orders_2('#skF_3','#skF_5','#skF_2'('#skF_3','#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_668])).

tff(c_697,plain,(
    m1_subset_1('#skF_2'('#skF_3','#skF_6','#skF_7'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_668])).

tff(c_698,plain,(
    ! [A_211,D_212,B_213,C_214] :
      ( r1_tarski(k3_orders_2(A_211,D_212,B_213),k3_orders_2(A_211,D_212,C_214))
      | ~ r2_orders_2(A_211,B_213,C_214)
      | ~ m1_subset_1(D_212,k1_zfmisc_1(u1_struct_0(A_211)))
      | ~ m1_subset_1(C_214,u1_struct_0(A_211))
      | ~ m1_subset_1(B_213,u1_struct_0(A_211))
      | ~ l1_orders_2(A_211)
      | ~ v5_orders_2(A_211)
      | ~ v4_orders_2(A_211)
      | ~ v3_orders_2(A_211)
      | v2_struct_0(A_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_714,plain,(
    ! [B_213] :
      ( r1_tarski(k3_orders_2('#skF_3','#skF_6',B_213),'#skF_7')
      | ~ r2_orders_2('#skF_3',B_213,'#skF_2'('#skF_3','#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_6','#skF_7'),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_213,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_650,c_698])).

tff(c_724,plain,(
    ! [B_213] :
      ( r1_tarski(k3_orders_2('#skF_3','#skF_6',B_213),'#skF_7')
      | ~ r2_orders_2('#skF_3',B_213,'#skF_2'('#skF_3','#skF_6','#skF_7'))
      | ~ m1_subset_1(B_213,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_697,c_46,c_714])).

tff(c_815,plain,(
    ! [B_218] :
      ( r1_tarski(k3_orders_2('#skF_3','#skF_6',B_218),'#skF_7')
      | ~ r2_orders_2('#skF_3',B_218,'#skF_2'('#skF_3','#skF_6','#skF_7'))
      | ~ m1_subset_1(B_218,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_724])).

tff(c_818,plain,
    ( r1_tarski(k3_orders_2('#skF_3','#skF_6','#skF_5'),'#skF_7')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_696,c_815])).

tff(c_821,plain,(
    r1_tarski(k3_orders_2('#skF_3','#skF_6','#skF_5'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_818])).

tff(c_628,plain,(
    ! [B_206,A_207,D_208,C_209] :
      ( r2_hidden(B_206,k3_orders_2(A_207,D_208,C_209))
      | ~ r2_hidden(B_206,D_208)
      | ~ r2_orders_2(A_207,B_206,C_209)
      | ~ m1_subset_1(D_208,k1_zfmisc_1(u1_struct_0(A_207)))
      | ~ m1_subset_1(C_209,u1_struct_0(A_207))
      | ~ m1_subset_1(B_206,u1_struct_0(A_207))
      | ~ l1_orders_2(A_207)
      | ~ v5_orders_2(A_207)
      | ~ v4_orders_2(A_207)
      | ~ v3_orders_2(A_207)
      | v2_struct_0(A_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_632,plain,(
    ! [B_206,C_209] :
      ( r2_hidden(B_206,k3_orders_2('#skF_3','#skF_6',C_209))
      | ~ r2_hidden(B_206,'#skF_6')
      | ~ r2_orders_2('#skF_3',B_206,C_209)
      | ~ m1_subset_1(C_209,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_206,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_46,c_628])).

tff(c_639,plain,(
    ! [B_206,C_209] :
      ( r2_hidden(B_206,k3_orders_2('#skF_3','#skF_6',C_209))
      | ~ r2_hidden(B_206,'#skF_6')
      | ~ r2_orders_2('#skF_3',B_206,C_209)
      | ~ m1_subset_1(C_209,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_206,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_632])).

tff(c_1320,plain,(
    ! [B_264,C_265] :
      ( r2_hidden(B_264,k3_orders_2('#skF_3','#skF_6',C_265))
      | ~ r2_hidden(B_264,'#skF_6')
      | ~ r2_orders_2('#skF_3',B_264,C_265)
      | ~ m1_subset_1(C_265,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_264,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_639])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2091,plain,(
    ! [B_320,B_321,C_322] :
      ( r2_hidden(B_320,B_321)
      | ~ r1_tarski(k3_orders_2('#skF_3','#skF_6',C_322),B_321)
      | ~ r2_hidden(B_320,'#skF_6')
      | ~ r2_orders_2('#skF_3',B_320,C_322)
      | ~ m1_subset_1(C_322,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_320,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1320,c_2])).

tff(c_2111,plain,(
    ! [B_320] :
      ( r2_hidden(B_320,'#skF_7')
      | ~ r2_hidden(B_320,'#skF_6')
      | ~ r2_orders_2('#skF_3',B_320,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_320,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_821,c_2091])).

tff(c_2143,plain,(
    ! [B_323] :
      ( r2_hidden(B_323,'#skF_7')
      | ~ r2_hidden(B_323,'#skF_6')
      | ~ r2_orders_2('#skF_3',B_323,'#skF_5')
      | ~ m1_subset_1(B_323,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2111])).

tff(c_2159,plain,
    ( r2_hidden('#skF_4','#skF_7')
    | ~ r2_hidden('#skF_4','#skF_6')
    | ~ r2_orders_2('#skF_3','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_2143])).

tff(c_2174,plain,(
    r2_hidden('#skF_4','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_2159])).

tff(c_2176,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_2174])).

tff(c_2177,plain,
    ( ~ m1_orders_2('#skF_7','#skF_3',k1_xboole_0)
    | k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_205])).

tff(c_2199,plain,(
    ~ m1_orders_2('#skF_7','#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_2177])).

tff(c_2243,plain,(
    ~ m1_orders_2('#skF_7','#skF_3','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2239,c_2199])).

tff(c_2255,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2243])).

tff(c_2257,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_2238])).

tff(c_2601,plain,(
    ! [A_384,B_385,C_386] :
      ( k3_orders_2(A_384,B_385,'#skF_2'(A_384,B_385,C_386)) = C_386
      | ~ m1_orders_2(C_386,A_384,B_385)
      | k1_xboole_0 = B_385
      | ~ m1_subset_1(C_386,k1_zfmisc_1(u1_struct_0(A_384)))
      | ~ m1_subset_1(B_385,k1_zfmisc_1(u1_struct_0(A_384)))
      | ~ l1_orders_2(A_384)
      | ~ v5_orders_2(A_384)
      | ~ v4_orders_2(A_384)
      | ~ v3_orders_2(A_384)
      | v2_struct_0(A_384) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2605,plain,(
    ! [B_385] :
      ( k3_orders_2('#skF_3',B_385,'#skF_2'('#skF_3',B_385,'#skF_7')) = '#skF_7'
      | ~ m1_orders_2('#skF_7','#skF_3',B_385)
      | k1_xboole_0 = B_385
      | ~ m1_subset_1(B_385,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_44,c_2601])).

tff(c_2614,plain,(
    ! [B_385] :
      ( k3_orders_2('#skF_3',B_385,'#skF_2'('#skF_3',B_385,'#skF_7')) = '#skF_7'
      | ~ m1_orders_2('#skF_7','#skF_3',B_385)
      | k1_xboole_0 = B_385
      | ~ m1_subset_1(B_385,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_2605])).

tff(c_2632,plain,(
    ! [B_389] :
      ( k3_orders_2('#skF_3',B_389,'#skF_2'('#skF_3',B_389,'#skF_7')) = '#skF_7'
      | ~ m1_orders_2('#skF_7','#skF_3',B_389)
      | k1_xboole_0 = B_389
      | ~ m1_subset_1(B_389,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2614])).

tff(c_2638,plain,
    ( k3_orders_2('#skF_3','#skF_6','#skF_2'('#skF_3','#skF_6','#skF_7')) = '#skF_7'
    | ~ m1_orders_2('#skF_7','#skF_3','#skF_6')
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_46,c_2632])).

tff(c_2643,plain,
    ( k3_orders_2('#skF_3','#skF_6','#skF_2'('#skF_3','#skF_6','#skF_7')) = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2638])).

tff(c_2644,plain,(
    k3_orders_2('#skF_3','#skF_6','#skF_2'('#skF_3','#skF_6','#skF_7')) = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_2257,c_2643])).

tff(c_2387,plain,(
    ! [A_354,B_355,C_356,D_357] :
      ( r2_orders_2(A_354,B_355,C_356)
      | ~ r2_hidden(B_355,k3_orders_2(A_354,D_357,C_356))
      | ~ m1_subset_1(D_357,k1_zfmisc_1(u1_struct_0(A_354)))
      | ~ m1_subset_1(C_356,u1_struct_0(A_354))
      | ~ m1_subset_1(B_355,u1_struct_0(A_354))
      | ~ l1_orders_2(A_354)
      | ~ v5_orders_2(A_354)
      | ~ v4_orders_2(A_354)
      | ~ v3_orders_2(A_354)
      | v2_struct_0(A_354) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2549,plain,(
    ! [A_376,C_377,D_378] :
      ( r2_orders_2(A_376,'#skF_5',C_377)
      | ~ m1_subset_1(D_378,k1_zfmisc_1(u1_struct_0(A_376)))
      | ~ m1_subset_1(C_377,u1_struct_0(A_376))
      | ~ m1_subset_1('#skF_5',u1_struct_0(A_376))
      | ~ l1_orders_2(A_376)
      | ~ v5_orders_2(A_376)
      | ~ v4_orders_2(A_376)
      | ~ v3_orders_2(A_376)
      | v2_struct_0(A_376)
      | ~ r1_tarski('#skF_7',k3_orders_2(A_376,D_378,C_377)) ) ),
    inference(resolution,[status(thm)],[c_98,c_2387])).

tff(c_2555,plain,(
    ! [C_377] :
      ( r2_orders_2('#skF_3','#skF_5',C_377)
      | ~ m1_subset_1(C_377,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_tarski('#skF_7',k3_orders_2('#skF_3','#skF_6',C_377)) ) ),
    inference(resolution,[status(thm)],[c_46,c_2549])).

tff(c_2566,plain,(
    ! [C_377] :
      ( r2_orders_2('#skF_3','#skF_5',C_377)
      | ~ m1_subset_1(C_377,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3')
      | ~ r1_tarski('#skF_7',k3_orders_2('#skF_3','#skF_6',C_377)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_48,c_2555])).

tff(c_2567,plain,(
    ! [C_377] :
      ( r2_orders_2('#skF_3','#skF_5',C_377)
      | ~ m1_subset_1(C_377,u1_struct_0('#skF_3'))
      | ~ r1_tarski('#skF_7',k3_orders_2('#skF_3','#skF_6',C_377)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2566])).

tff(c_2662,plain,
    ( r2_orders_2('#skF_3','#skF_5','#skF_2'('#skF_3','#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_6','#skF_7'),u1_struct_0('#skF_3'))
    | ~ r1_tarski('#skF_7','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_2644,c_2567])).

tff(c_2670,plain,
    ( r2_orders_2('#skF_3','#skF_5','#skF_2'('#skF_3','#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_6','#skF_7'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_2662])).

tff(c_2678,plain,(
    ~ m1_subset_1('#skF_2'('#skF_3','#skF_6','#skF_7'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2670])).

tff(c_2681,plain,
    ( ~ m1_orders_2('#skF_7','#skF_3','#skF_6')
    | k1_xboole_0 = '#skF_6'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_2678])).

tff(c_2693,plain,
    ( k1_xboole_0 = '#skF_6'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_46,c_44,c_36,c_2681])).

tff(c_2695,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2257,c_2693])).

tff(c_2696,plain,(
    r2_orders_2('#skF_3','#skF_5','#skF_2'('#skF_3','#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_2670])).

tff(c_2697,plain,(
    m1_subset_1('#skF_2'('#skF_3','#skF_6','#skF_7'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2670])).

tff(c_2698,plain,(
    ! [A_391,D_392,B_393,C_394] :
      ( r1_tarski(k3_orders_2(A_391,D_392,B_393),k3_orders_2(A_391,D_392,C_394))
      | ~ r2_orders_2(A_391,B_393,C_394)
      | ~ m1_subset_1(D_392,k1_zfmisc_1(u1_struct_0(A_391)))
      | ~ m1_subset_1(C_394,u1_struct_0(A_391))
      | ~ m1_subset_1(B_393,u1_struct_0(A_391))
      | ~ l1_orders_2(A_391)
      | ~ v5_orders_2(A_391)
      | ~ v4_orders_2(A_391)
      | ~ v3_orders_2(A_391)
      | v2_struct_0(A_391) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_2714,plain,(
    ! [B_393] :
      ( r1_tarski(k3_orders_2('#skF_3','#skF_6',B_393),'#skF_7')
      | ~ r2_orders_2('#skF_3',B_393,'#skF_2'('#skF_3','#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_6','#skF_7'),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_393,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2644,c_2698])).

tff(c_2724,plain,(
    ! [B_393] :
      ( r1_tarski(k3_orders_2('#skF_3','#skF_6',B_393),'#skF_7')
      | ~ r2_orders_2('#skF_3',B_393,'#skF_2'('#skF_3','#skF_6','#skF_7'))
      | ~ m1_subset_1(B_393,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_2697,c_46,c_2714])).

tff(c_2990,plain,(
    ! [B_412] :
      ( r1_tarski(k3_orders_2('#skF_3','#skF_6',B_412),'#skF_7')
      | ~ r2_orders_2('#skF_3',B_412,'#skF_2'('#skF_3','#skF_6','#skF_7'))
      | ~ m1_subset_1(B_412,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2724])).

tff(c_2993,plain,
    ( r1_tarski(k3_orders_2('#skF_3','#skF_6','#skF_5'),'#skF_7')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2696,c_2990])).

tff(c_2996,plain,(
    r1_tarski(k3_orders_2('#skF_3','#skF_6','#skF_5'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2993])).

tff(c_2867,plain,(
    ! [B_403,A_404,D_405,C_406] :
      ( r2_hidden(B_403,k3_orders_2(A_404,D_405,C_406))
      | ~ r2_hidden(B_403,D_405)
      | ~ r2_orders_2(A_404,B_403,C_406)
      | ~ m1_subset_1(D_405,k1_zfmisc_1(u1_struct_0(A_404)))
      | ~ m1_subset_1(C_406,u1_struct_0(A_404))
      | ~ m1_subset_1(B_403,u1_struct_0(A_404))
      | ~ l1_orders_2(A_404)
      | ~ v5_orders_2(A_404)
      | ~ v4_orders_2(A_404)
      | ~ v3_orders_2(A_404)
      | v2_struct_0(A_404) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2873,plain,(
    ! [B_403,C_406] :
      ( r2_hidden(B_403,k3_orders_2('#skF_3','#skF_6',C_406))
      | ~ r2_hidden(B_403,'#skF_6')
      | ~ r2_orders_2('#skF_3',B_403,C_406)
      | ~ m1_subset_1(C_406,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_403,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_46,c_2867])).

tff(c_2884,plain,(
    ! [B_403,C_406] :
      ( r2_hidden(B_403,k3_orders_2('#skF_3','#skF_6',C_406))
      | ~ r2_hidden(B_403,'#skF_6')
      | ~ r2_orders_2('#skF_3',B_403,C_406)
      | ~ m1_subset_1(C_406,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_403,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_2873])).

tff(c_3078,plain,(
    ! [B_420,C_421] :
      ( r2_hidden(B_420,k3_orders_2('#skF_3','#skF_6',C_421))
      | ~ r2_hidden(B_420,'#skF_6')
      | ~ r2_orders_2('#skF_3',B_420,C_421)
      | ~ m1_subset_1(C_421,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_420,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2884])).

tff(c_4040,plain,(
    ! [B_495,B_496,C_497] :
      ( r2_hidden(B_495,B_496)
      | ~ r1_tarski(k3_orders_2('#skF_3','#skF_6',C_497),B_496)
      | ~ r2_hidden(B_495,'#skF_6')
      | ~ r2_orders_2('#skF_3',B_495,C_497)
      | ~ m1_subset_1(C_497,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_495,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_3078,c_2])).

tff(c_4060,plain,(
    ! [B_495] :
      ( r2_hidden(B_495,'#skF_7')
      | ~ r2_hidden(B_495,'#skF_6')
      | ~ r2_orders_2('#skF_3',B_495,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_495,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_2996,c_4040])).

tff(c_4092,plain,(
    ! [B_498] :
      ( r2_hidden(B_498,'#skF_7')
      | ~ r2_hidden(B_498,'#skF_6')
      | ~ r2_orders_2('#skF_3',B_498,'#skF_5')
      | ~ m1_subset_1(B_498,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_4060])).

tff(c_4111,plain,
    ( r2_hidden('#skF_4','#skF_7')
    | ~ r2_hidden('#skF_4','#skF_6')
    | ~ r2_orders_2('#skF_3','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_4092])).

tff(c_4127,plain,(
    r2_hidden('#skF_4','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_4111])).

tff(c_4129,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_4127])).

tff(c_4130,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_2177])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_100,plain,(
    ! [B_103] :
      ( r2_hidden('#skF_5',B_103)
      | ~ r1_tarski('#skF_7',B_103) ) ),
    inference(resolution,[status(thm)],[c_38,c_90])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( ~ r1_tarski(B_11,A_10)
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_127,plain,(
    ! [B_108] :
      ( ~ r1_tarski(B_108,'#skF_5')
      | ~ r1_tarski('#skF_7',B_108) ) ),
    inference(resolution,[status(thm)],[c_100,c_12])).

tff(c_135,plain,(
    ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_127])).

tff(c_4139,plain,(
    ~ r1_tarski('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4130,c_135])).

tff(c_4144,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_4139])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:04:46 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.70/2.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.06/2.13  
% 6.06/2.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.06/2.14  %$ r2_orders_2 > m1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 6.06/2.14  
% 6.06/2.14  %Foreground sorts:
% 6.06/2.14  
% 6.06/2.14  
% 6.06/2.14  %Background operators:
% 6.06/2.14  
% 6.06/2.14  
% 6.06/2.14  %Foreground operators:
% 6.06/2.14  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.06/2.14  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 6.06/2.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.06/2.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.06/2.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.06/2.14  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 6.06/2.14  tff('#skF_7', type, '#skF_7': $i).
% 6.06/2.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.06/2.14  tff('#skF_5', type, '#skF_5': $i).
% 6.06/2.14  tff('#skF_6', type, '#skF_6': $i).
% 6.06/2.14  tff('#skF_3', type, '#skF_3': $i).
% 6.06/2.14  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.06/2.14  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 6.06/2.14  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 6.06/2.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.06/2.14  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 6.06/2.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.06/2.14  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 6.06/2.14  tff('#skF_4', type, '#skF_4': $i).
% 6.06/2.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.06/2.14  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 6.06/2.14  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.06/2.14  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.06/2.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.06/2.14  
% 6.06/2.17  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 6.06/2.17  tff(f_164, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(A))) => ((((r2_orders_2(A, B, C) & r2_hidden(B, D)) & r2_hidden(C, E)) & m1_orders_2(E, A, D)) => r2_hidden(B, E)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_orders_2)).
% 6.06/2.17  tff(f_80, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((~(B = k1_xboole_0) => (m1_orders_2(C, A, B) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(A)) & r2_hidden(D, B)) & (C = k3_orders_2(A, B, D)))))) & ((B = k1_xboole_0) => (m1_orders_2(C, A, B) <=> (C = k1_xboole_0)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d15_orders_2)).
% 6.06/2.17  tff(f_106, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_orders_2)).
% 6.06/2.17  tff(f_130, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_orders_2(A, B, C) => r1_tarski(k3_orders_2(A, D, B), k3_orders_2(A, D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_orders_2)).
% 6.06/2.17  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.06/2.17  tff(f_45, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 6.06/2.17  tff(c_72, plain, (![A_95, B_96]: (r2_hidden('#skF_1'(A_95, B_96), A_95) | r1_tarski(A_95, B_96))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.06/2.17  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.06/2.17  tff(c_80, plain, (![A_95]: (r1_tarski(A_95, A_95))), inference(resolution, [status(thm)], [c_72, c_4])).
% 6.06/2.17  tff(c_34, plain, (~r2_hidden('#skF_4', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_164])).
% 6.06/2.17  tff(c_42, plain, (r2_orders_2('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_164])).
% 6.06/2.17  tff(c_40, plain, (r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_164])).
% 6.06/2.17  tff(c_50, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_164])).
% 6.06/2.17  tff(c_48, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_164])).
% 6.06/2.17  tff(c_60, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_164])).
% 6.06/2.17  tff(c_36, plain, (m1_orders_2('#skF_7', '#skF_3', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_164])).
% 6.06/2.17  tff(c_46, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_164])).
% 6.06/2.17  tff(c_58, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_164])).
% 6.06/2.17  tff(c_56, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_164])).
% 6.06/2.17  tff(c_54, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_164])).
% 6.06/2.17  tff(c_52, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_164])).
% 6.06/2.17  tff(c_44, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_164])).
% 6.06/2.17  tff(c_2208, plain, (![A_329, B_330, C_331]: (r2_hidden('#skF_2'(A_329, B_330, C_331), B_330) | ~m1_orders_2(C_331, A_329, B_330) | k1_xboole_0=B_330 | ~m1_subset_1(C_331, k1_zfmisc_1(u1_struct_0(A_329))) | ~m1_subset_1(B_330, k1_zfmisc_1(u1_struct_0(A_329))) | ~l1_orders_2(A_329) | ~v5_orders_2(A_329) | ~v4_orders_2(A_329) | ~v3_orders_2(A_329) | v2_struct_0(A_329))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.06/2.17  tff(c_2212, plain, (![B_330]: (r2_hidden('#skF_2'('#skF_3', B_330, '#skF_7'), B_330) | ~m1_orders_2('#skF_7', '#skF_3', B_330) | k1_xboole_0=B_330 | ~m1_subset_1(B_330, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_2208])).
% 6.06/2.17  tff(c_2221, plain, (![B_330]: (r2_hidden('#skF_2'('#skF_3', B_330, '#skF_7'), B_330) | ~m1_orders_2('#skF_7', '#skF_3', B_330) | k1_xboole_0=B_330 | ~m1_subset_1(B_330, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_2212])).
% 6.06/2.17  tff(c_2227, plain, (![B_332]: (r2_hidden('#skF_2'('#skF_3', B_332, '#skF_7'), B_332) | ~m1_orders_2('#skF_7', '#skF_3', B_332) | k1_xboole_0=B_332 | ~m1_subset_1(B_332, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_2221])).
% 6.06/2.17  tff(c_2233, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_6', '#skF_7'), '#skF_6') | ~m1_orders_2('#skF_7', '#skF_3', '#skF_6') | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_46, c_2227])).
% 6.06/2.17  tff(c_2238, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_6', '#skF_7'), '#skF_6') | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2233])).
% 6.06/2.17  tff(c_2239, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_2238])).
% 6.06/2.17  tff(c_218, plain, (![A_131, B_132, C_133]: (r2_hidden('#skF_2'(A_131, B_132, C_133), B_132) | ~m1_orders_2(C_133, A_131, B_132) | k1_xboole_0=B_132 | ~m1_subset_1(C_133, k1_zfmisc_1(u1_struct_0(A_131))) | ~m1_subset_1(B_132, k1_zfmisc_1(u1_struct_0(A_131))) | ~l1_orders_2(A_131) | ~v5_orders_2(A_131) | ~v4_orders_2(A_131) | ~v3_orders_2(A_131) | v2_struct_0(A_131))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.06/2.17  tff(c_220, plain, (![B_132]: (r2_hidden('#skF_2'('#skF_3', B_132, '#skF_7'), B_132) | ~m1_orders_2('#skF_7', '#skF_3', B_132) | k1_xboole_0=B_132 | ~m1_subset_1(B_132, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_218])).
% 6.06/2.17  tff(c_225, plain, (![B_132]: (r2_hidden('#skF_2'('#skF_3', B_132, '#skF_7'), B_132) | ~m1_orders_2('#skF_7', '#skF_3', B_132) | k1_xboole_0=B_132 | ~m1_subset_1(B_132, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_220])).
% 6.06/2.17  tff(c_248, plain, (![B_138]: (r2_hidden('#skF_2'('#skF_3', B_138, '#skF_7'), B_138) | ~m1_orders_2('#skF_7', '#skF_3', B_138) | k1_xboole_0=B_138 | ~m1_subset_1(B_138, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_225])).
% 6.06/2.17  tff(c_252, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_6', '#skF_7'), '#skF_6') | ~m1_orders_2('#skF_7', '#skF_3', '#skF_6') | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_46, c_248])).
% 6.06/2.17  tff(c_256, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_6', '#skF_7'), '#skF_6') | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_252])).
% 6.06/2.17  tff(c_257, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_256])).
% 6.06/2.17  tff(c_197, plain, (![C_125, A_126]: (k1_xboole_0=C_125 | ~m1_orders_2(C_125, A_126, k1_xboole_0) | ~m1_subset_1(C_125, k1_zfmisc_1(u1_struct_0(A_126))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_126))) | ~l1_orders_2(A_126) | ~v5_orders_2(A_126) | ~v4_orders_2(A_126) | ~v3_orders_2(A_126) | v2_struct_0(A_126))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.06/2.17  tff(c_199, plain, (k1_xboole_0='#skF_7' | ~m1_orders_2('#skF_7', '#skF_3', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_44, c_197])).
% 6.06/2.17  tff(c_204, plain, (k1_xboole_0='#skF_7' | ~m1_orders_2('#skF_7', '#skF_3', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_199])).
% 6.06/2.17  tff(c_205, plain, (k1_xboole_0='#skF_7' | ~m1_orders_2('#skF_7', '#skF_3', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_60, c_204])).
% 6.06/2.17  tff(c_210, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_205])).
% 6.06/2.17  tff(c_260, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_257, c_210])).
% 6.06/2.17  tff(c_269, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_260])).
% 6.06/2.17  tff(c_271, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_256])).
% 6.06/2.17  tff(c_24, plain, (![A_12, B_24, C_30]: (m1_subset_1('#skF_2'(A_12, B_24, C_30), u1_struct_0(A_12)) | ~m1_orders_2(C_30, A_12, B_24) | k1_xboole_0=B_24 | ~m1_subset_1(C_30, k1_zfmisc_1(u1_struct_0(A_12))) | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0(A_12))) | ~l1_orders_2(A_12) | ~v5_orders_2(A_12) | ~v4_orders_2(A_12) | ~v3_orders_2(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.06/2.17  tff(c_615, plain, (![A_203, B_204, C_205]: (k3_orders_2(A_203, B_204, '#skF_2'(A_203, B_204, C_205))=C_205 | ~m1_orders_2(C_205, A_203, B_204) | k1_xboole_0=B_204 | ~m1_subset_1(C_205, k1_zfmisc_1(u1_struct_0(A_203))) | ~m1_subset_1(B_204, k1_zfmisc_1(u1_struct_0(A_203))) | ~l1_orders_2(A_203) | ~v5_orders_2(A_203) | ~v4_orders_2(A_203) | ~v3_orders_2(A_203) | v2_struct_0(A_203))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.06/2.17  tff(c_617, plain, (![B_204]: (k3_orders_2('#skF_3', B_204, '#skF_2'('#skF_3', B_204, '#skF_7'))='#skF_7' | ~m1_orders_2('#skF_7', '#skF_3', B_204) | k1_xboole_0=B_204 | ~m1_subset_1(B_204, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_615])).
% 6.06/2.17  tff(c_622, plain, (![B_204]: (k3_orders_2('#skF_3', B_204, '#skF_2'('#skF_3', B_204, '#skF_7'))='#skF_7' | ~m1_orders_2('#skF_7', '#skF_3', B_204) | k1_xboole_0=B_204 | ~m1_subset_1(B_204, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_617])).
% 6.06/2.17  tff(c_641, plain, (![B_210]: (k3_orders_2('#skF_3', B_210, '#skF_2'('#skF_3', B_210, '#skF_7'))='#skF_7' | ~m1_orders_2('#skF_7', '#skF_3', B_210) | k1_xboole_0=B_210 | ~m1_subset_1(B_210, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_622])).
% 6.06/2.17  tff(c_645, plain, (k3_orders_2('#skF_3', '#skF_6', '#skF_2'('#skF_3', '#skF_6', '#skF_7'))='#skF_7' | ~m1_orders_2('#skF_7', '#skF_3', '#skF_6') | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_46, c_641])).
% 6.06/2.17  tff(c_649, plain, (k3_orders_2('#skF_3', '#skF_6', '#skF_2'('#skF_3', '#skF_6', '#skF_7'))='#skF_7' | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_645])).
% 6.06/2.17  tff(c_650, plain, (k3_orders_2('#skF_3', '#skF_6', '#skF_2'('#skF_3', '#skF_6', '#skF_7'))='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_271, c_649])).
% 6.06/2.17  tff(c_28, plain, (![B_42, D_48, A_34, C_46]: (r2_hidden(B_42, D_48) | ~r2_hidden(B_42, k3_orders_2(A_34, D_48, C_46)) | ~m1_subset_1(D_48, k1_zfmisc_1(u1_struct_0(A_34))) | ~m1_subset_1(C_46, u1_struct_0(A_34)) | ~m1_subset_1(B_42, u1_struct_0(A_34)) | ~l1_orders_2(A_34) | ~v5_orders_2(A_34) | ~v4_orders_2(A_34) | ~v3_orders_2(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.06/2.17  tff(c_664, plain, (![B_42]: (r2_hidden(B_42, '#skF_6') | ~r2_hidden(B_42, '#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_2'('#skF_3', '#skF_6', '#skF_7'), u1_struct_0('#skF_3')) | ~m1_subset_1(B_42, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_650, c_28])).
% 6.06/2.17  tff(c_673, plain, (![B_42]: (r2_hidden(B_42, '#skF_6') | ~r2_hidden(B_42, '#skF_7') | ~m1_subset_1('#skF_2'('#skF_3', '#skF_6', '#skF_7'), u1_struct_0('#skF_3')) | ~m1_subset_1(B_42, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_46, c_664])).
% 6.06/2.17  tff(c_674, plain, (![B_42]: (r2_hidden(B_42, '#skF_6') | ~r2_hidden(B_42, '#skF_7') | ~m1_subset_1('#skF_2'('#skF_3', '#skF_6', '#skF_7'), u1_struct_0('#skF_3')) | ~m1_subset_1(B_42, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_60, c_673])).
% 6.06/2.17  tff(c_677, plain, (~m1_subset_1('#skF_2'('#skF_3', '#skF_6', '#skF_7'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_674])).
% 6.06/2.17  tff(c_680, plain, (~m1_orders_2('#skF_7', '#skF_3', '#skF_6') | k1_xboole_0='#skF_6' | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_24, c_677])).
% 6.06/2.17  tff(c_689, plain, (k1_xboole_0='#skF_6' | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_46, c_44, c_36, c_680])).
% 6.06/2.17  tff(c_691, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_271, c_689])).
% 6.06/2.17  tff(c_693, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_6', '#skF_7'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_674])).
% 6.06/2.17  tff(c_38, plain, (r2_hidden('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_164])).
% 6.06/2.17  tff(c_90, plain, (![C_100, B_101, A_102]: (r2_hidden(C_100, B_101) | ~r2_hidden(C_100, A_102) | ~r1_tarski(A_102, B_101))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.06/2.17  tff(c_98, plain, (![B_101]: (r2_hidden('#skF_5', B_101) | ~r1_tarski('#skF_7', B_101))), inference(resolution, [status(thm)], [c_38, c_90])).
% 6.06/2.17  tff(c_534, plain, (![A_183, B_184, C_185, D_186]: (r2_orders_2(A_183, B_184, C_185) | ~r2_hidden(B_184, k3_orders_2(A_183, D_186, C_185)) | ~m1_subset_1(D_186, k1_zfmisc_1(u1_struct_0(A_183))) | ~m1_subset_1(C_185, u1_struct_0(A_183)) | ~m1_subset_1(B_184, u1_struct_0(A_183)) | ~l1_orders_2(A_183) | ~v5_orders_2(A_183) | ~v4_orders_2(A_183) | ~v3_orders_2(A_183) | v2_struct_0(A_183))), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.06/2.17  tff(c_586, plain, (![A_194, C_195, D_196]: (r2_orders_2(A_194, '#skF_5', C_195) | ~m1_subset_1(D_196, k1_zfmisc_1(u1_struct_0(A_194))) | ~m1_subset_1(C_195, u1_struct_0(A_194)) | ~m1_subset_1('#skF_5', u1_struct_0(A_194)) | ~l1_orders_2(A_194) | ~v5_orders_2(A_194) | ~v4_orders_2(A_194) | ~v3_orders_2(A_194) | v2_struct_0(A_194) | ~r1_tarski('#skF_7', k3_orders_2(A_194, D_196, C_195)))), inference(resolution, [status(thm)], [c_98, c_534])).
% 6.06/2.17  tff(c_590, plain, (![C_195]: (r2_orders_2('#skF_3', '#skF_5', C_195) | ~m1_subset_1(C_195, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3') | ~r1_tarski('#skF_7', k3_orders_2('#skF_3', '#skF_6', C_195)))), inference(resolution, [status(thm)], [c_46, c_586])).
% 6.06/2.17  tff(c_597, plain, (![C_195]: (r2_orders_2('#skF_3', '#skF_5', C_195) | ~m1_subset_1(C_195, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3') | ~r1_tarski('#skF_7', k3_orders_2('#skF_3', '#skF_6', C_195)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_48, c_590])).
% 6.06/2.17  tff(c_598, plain, (![C_195]: (r2_orders_2('#skF_3', '#skF_5', C_195) | ~m1_subset_1(C_195, u1_struct_0('#skF_3')) | ~r1_tarski('#skF_7', k3_orders_2('#skF_3', '#skF_6', C_195)))), inference(negUnitSimplification, [status(thm)], [c_60, c_597])).
% 6.06/2.17  tff(c_657, plain, (r2_orders_2('#skF_3', '#skF_5', '#skF_2'('#skF_3', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_2'('#skF_3', '#skF_6', '#skF_7'), u1_struct_0('#skF_3')) | ~r1_tarski('#skF_7', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_650, c_598])).
% 6.06/2.17  tff(c_668, plain, (r2_orders_2('#skF_3', '#skF_5', '#skF_2'('#skF_3', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_2'('#skF_3', '#skF_6', '#skF_7'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_657])).
% 6.06/2.17  tff(c_676, plain, (~m1_subset_1('#skF_2'('#skF_3', '#skF_6', '#skF_7'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_668])).
% 6.06/2.17  tff(c_695, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_693, c_676])).
% 6.06/2.17  tff(c_696, plain, (r2_orders_2('#skF_3', '#skF_5', '#skF_2'('#skF_3', '#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_668])).
% 6.06/2.17  tff(c_697, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_6', '#skF_7'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_668])).
% 6.06/2.17  tff(c_698, plain, (![A_211, D_212, B_213, C_214]: (r1_tarski(k3_orders_2(A_211, D_212, B_213), k3_orders_2(A_211, D_212, C_214)) | ~r2_orders_2(A_211, B_213, C_214) | ~m1_subset_1(D_212, k1_zfmisc_1(u1_struct_0(A_211))) | ~m1_subset_1(C_214, u1_struct_0(A_211)) | ~m1_subset_1(B_213, u1_struct_0(A_211)) | ~l1_orders_2(A_211) | ~v5_orders_2(A_211) | ~v4_orders_2(A_211) | ~v3_orders_2(A_211) | v2_struct_0(A_211))), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.06/2.17  tff(c_714, plain, (![B_213]: (r1_tarski(k3_orders_2('#skF_3', '#skF_6', B_213), '#skF_7') | ~r2_orders_2('#skF_3', B_213, '#skF_2'('#skF_3', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_2'('#skF_3', '#skF_6', '#skF_7'), u1_struct_0('#skF_3')) | ~m1_subset_1(B_213, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_650, c_698])).
% 6.06/2.17  tff(c_724, plain, (![B_213]: (r1_tarski(k3_orders_2('#skF_3', '#skF_6', B_213), '#skF_7') | ~r2_orders_2('#skF_3', B_213, '#skF_2'('#skF_3', '#skF_6', '#skF_7')) | ~m1_subset_1(B_213, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_697, c_46, c_714])).
% 6.06/2.17  tff(c_815, plain, (![B_218]: (r1_tarski(k3_orders_2('#skF_3', '#skF_6', B_218), '#skF_7') | ~r2_orders_2('#skF_3', B_218, '#skF_2'('#skF_3', '#skF_6', '#skF_7')) | ~m1_subset_1(B_218, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_60, c_724])).
% 6.06/2.17  tff(c_818, plain, (r1_tarski(k3_orders_2('#skF_3', '#skF_6', '#skF_5'), '#skF_7') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_696, c_815])).
% 6.06/2.17  tff(c_821, plain, (r1_tarski(k3_orders_2('#skF_3', '#skF_6', '#skF_5'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_818])).
% 6.06/2.17  tff(c_628, plain, (![B_206, A_207, D_208, C_209]: (r2_hidden(B_206, k3_orders_2(A_207, D_208, C_209)) | ~r2_hidden(B_206, D_208) | ~r2_orders_2(A_207, B_206, C_209) | ~m1_subset_1(D_208, k1_zfmisc_1(u1_struct_0(A_207))) | ~m1_subset_1(C_209, u1_struct_0(A_207)) | ~m1_subset_1(B_206, u1_struct_0(A_207)) | ~l1_orders_2(A_207) | ~v5_orders_2(A_207) | ~v4_orders_2(A_207) | ~v3_orders_2(A_207) | v2_struct_0(A_207))), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.06/2.17  tff(c_632, plain, (![B_206, C_209]: (r2_hidden(B_206, k3_orders_2('#skF_3', '#skF_6', C_209)) | ~r2_hidden(B_206, '#skF_6') | ~r2_orders_2('#skF_3', B_206, C_209) | ~m1_subset_1(C_209, u1_struct_0('#skF_3')) | ~m1_subset_1(B_206, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_628])).
% 6.06/2.17  tff(c_639, plain, (![B_206, C_209]: (r2_hidden(B_206, k3_orders_2('#skF_3', '#skF_6', C_209)) | ~r2_hidden(B_206, '#skF_6') | ~r2_orders_2('#skF_3', B_206, C_209) | ~m1_subset_1(C_209, u1_struct_0('#skF_3')) | ~m1_subset_1(B_206, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_632])).
% 6.06/2.17  tff(c_1320, plain, (![B_264, C_265]: (r2_hidden(B_264, k3_orders_2('#skF_3', '#skF_6', C_265)) | ~r2_hidden(B_264, '#skF_6') | ~r2_orders_2('#skF_3', B_264, C_265) | ~m1_subset_1(C_265, u1_struct_0('#skF_3')) | ~m1_subset_1(B_264, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_60, c_639])).
% 6.06/2.17  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.06/2.17  tff(c_2091, plain, (![B_320, B_321, C_322]: (r2_hidden(B_320, B_321) | ~r1_tarski(k3_orders_2('#skF_3', '#skF_6', C_322), B_321) | ~r2_hidden(B_320, '#skF_6') | ~r2_orders_2('#skF_3', B_320, C_322) | ~m1_subset_1(C_322, u1_struct_0('#skF_3')) | ~m1_subset_1(B_320, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_1320, c_2])).
% 6.06/2.17  tff(c_2111, plain, (![B_320]: (r2_hidden(B_320, '#skF_7') | ~r2_hidden(B_320, '#skF_6') | ~r2_orders_2('#skF_3', B_320, '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1(B_320, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_821, c_2091])).
% 6.06/2.17  tff(c_2143, plain, (![B_323]: (r2_hidden(B_323, '#skF_7') | ~r2_hidden(B_323, '#skF_6') | ~r2_orders_2('#skF_3', B_323, '#skF_5') | ~m1_subset_1(B_323, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_2111])).
% 6.06/2.17  tff(c_2159, plain, (r2_hidden('#skF_4', '#skF_7') | ~r2_hidden('#skF_4', '#skF_6') | ~r2_orders_2('#skF_3', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_50, c_2143])).
% 6.06/2.17  tff(c_2174, plain, (r2_hidden('#skF_4', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_2159])).
% 6.06/2.17  tff(c_2176, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_2174])).
% 6.06/2.17  tff(c_2177, plain, (~m1_orders_2('#skF_7', '#skF_3', k1_xboole_0) | k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_205])).
% 6.06/2.17  tff(c_2199, plain, (~m1_orders_2('#skF_7', '#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_2177])).
% 6.06/2.17  tff(c_2243, plain, (~m1_orders_2('#skF_7', '#skF_3', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2239, c_2199])).
% 6.06/2.17  tff(c_2255, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_2243])).
% 6.06/2.17  tff(c_2257, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_2238])).
% 6.06/2.17  tff(c_2601, plain, (![A_384, B_385, C_386]: (k3_orders_2(A_384, B_385, '#skF_2'(A_384, B_385, C_386))=C_386 | ~m1_orders_2(C_386, A_384, B_385) | k1_xboole_0=B_385 | ~m1_subset_1(C_386, k1_zfmisc_1(u1_struct_0(A_384))) | ~m1_subset_1(B_385, k1_zfmisc_1(u1_struct_0(A_384))) | ~l1_orders_2(A_384) | ~v5_orders_2(A_384) | ~v4_orders_2(A_384) | ~v3_orders_2(A_384) | v2_struct_0(A_384))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.06/2.17  tff(c_2605, plain, (![B_385]: (k3_orders_2('#skF_3', B_385, '#skF_2'('#skF_3', B_385, '#skF_7'))='#skF_7' | ~m1_orders_2('#skF_7', '#skF_3', B_385) | k1_xboole_0=B_385 | ~m1_subset_1(B_385, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_2601])).
% 6.06/2.17  tff(c_2614, plain, (![B_385]: (k3_orders_2('#skF_3', B_385, '#skF_2'('#skF_3', B_385, '#skF_7'))='#skF_7' | ~m1_orders_2('#skF_7', '#skF_3', B_385) | k1_xboole_0=B_385 | ~m1_subset_1(B_385, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_2605])).
% 6.06/2.17  tff(c_2632, plain, (![B_389]: (k3_orders_2('#skF_3', B_389, '#skF_2'('#skF_3', B_389, '#skF_7'))='#skF_7' | ~m1_orders_2('#skF_7', '#skF_3', B_389) | k1_xboole_0=B_389 | ~m1_subset_1(B_389, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_2614])).
% 6.06/2.17  tff(c_2638, plain, (k3_orders_2('#skF_3', '#skF_6', '#skF_2'('#skF_3', '#skF_6', '#skF_7'))='#skF_7' | ~m1_orders_2('#skF_7', '#skF_3', '#skF_6') | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_46, c_2632])).
% 6.06/2.17  tff(c_2643, plain, (k3_orders_2('#skF_3', '#skF_6', '#skF_2'('#skF_3', '#skF_6', '#skF_7'))='#skF_7' | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2638])).
% 6.06/2.17  tff(c_2644, plain, (k3_orders_2('#skF_3', '#skF_6', '#skF_2'('#skF_3', '#skF_6', '#skF_7'))='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_2257, c_2643])).
% 6.06/2.17  tff(c_2387, plain, (![A_354, B_355, C_356, D_357]: (r2_orders_2(A_354, B_355, C_356) | ~r2_hidden(B_355, k3_orders_2(A_354, D_357, C_356)) | ~m1_subset_1(D_357, k1_zfmisc_1(u1_struct_0(A_354))) | ~m1_subset_1(C_356, u1_struct_0(A_354)) | ~m1_subset_1(B_355, u1_struct_0(A_354)) | ~l1_orders_2(A_354) | ~v5_orders_2(A_354) | ~v4_orders_2(A_354) | ~v3_orders_2(A_354) | v2_struct_0(A_354))), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.06/2.17  tff(c_2549, plain, (![A_376, C_377, D_378]: (r2_orders_2(A_376, '#skF_5', C_377) | ~m1_subset_1(D_378, k1_zfmisc_1(u1_struct_0(A_376))) | ~m1_subset_1(C_377, u1_struct_0(A_376)) | ~m1_subset_1('#skF_5', u1_struct_0(A_376)) | ~l1_orders_2(A_376) | ~v5_orders_2(A_376) | ~v4_orders_2(A_376) | ~v3_orders_2(A_376) | v2_struct_0(A_376) | ~r1_tarski('#skF_7', k3_orders_2(A_376, D_378, C_377)))), inference(resolution, [status(thm)], [c_98, c_2387])).
% 6.06/2.17  tff(c_2555, plain, (![C_377]: (r2_orders_2('#skF_3', '#skF_5', C_377) | ~m1_subset_1(C_377, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3') | ~r1_tarski('#skF_7', k3_orders_2('#skF_3', '#skF_6', C_377)))), inference(resolution, [status(thm)], [c_46, c_2549])).
% 6.06/2.17  tff(c_2566, plain, (![C_377]: (r2_orders_2('#skF_3', '#skF_5', C_377) | ~m1_subset_1(C_377, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3') | ~r1_tarski('#skF_7', k3_orders_2('#skF_3', '#skF_6', C_377)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_48, c_2555])).
% 6.06/2.17  tff(c_2567, plain, (![C_377]: (r2_orders_2('#skF_3', '#skF_5', C_377) | ~m1_subset_1(C_377, u1_struct_0('#skF_3')) | ~r1_tarski('#skF_7', k3_orders_2('#skF_3', '#skF_6', C_377)))), inference(negUnitSimplification, [status(thm)], [c_60, c_2566])).
% 6.06/2.17  tff(c_2662, plain, (r2_orders_2('#skF_3', '#skF_5', '#skF_2'('#skF_3', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_2'('#skF_3', '#skF_6', '#skF_7'), u1_struct_0('#skF_3')) | ~r1_tarski('#skF_7', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_2644, c_2567])).
% 6.06/2.17  tff(c_2670, plain, (r2_orders_2('#skF_3', '#skF_5', '#skF_2'('#skF_3', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_2'('#skF_3', '#skF_6', '#skF_7'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_2662])).
% 6.06/2.17  tff(c_2678, plain, (~m1_subset_1('#skF_2'('#skF_3', '#skF_6', '#skF_7'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_2670])).
% 6.06/2.17  tff(c_2681, plain, (~m1_orders_2('#skF_7', '#skF_3', '#skF_6') | k1_xboole_0='#skF_6' | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_24, c_2678])).
% 6.06/2.17  tff(c_2693, plain, (k1_xboole_0='#skF_6' | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_46, c_44, c_36, c_2681])).
% 6.06/2.17  tff(c_2695, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_2257, c_2693])).
% 6.06/2.17  tff(c_2696, plain, (r2_orders_2('#skF_3', '#skF_5', '#skF_2'('#skF_3', '#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_2670])).
% 6.06/2.17  tff(c_2697, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_6', '#skF_7'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_2670])).
% 6.06/2.17  tff(c_2698, plain, (![A_391, D_392, B_393, C_394]: (r1_tarski(k3_orders_2(A_391, D_392, B_393), k3_orders_2(A_391, D_392, C_394)) | ~r2_orders_2(A_391, B_393, C_394) | ~m1_subset_1(D_392, k1_zfmisc_1(u1_struct_0(A_391))) | ~m1_subset_1(C_394, u1_struct_0(A_391)) | ~m1_subset_1(B_393, u1_struct_0(A_391)) | ~l1_orders_2(A_391) | ~v5_orders_2(A_391) | ~v4_orders_2(A_391) | ~v3_orders_2(A_391) | v2_struct_0(A_391))), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.06/2.17  tff(c_2714, plain, (![B_393]: (r1_tarski(k3_orders_2('#skF_3', '#skF_6', B_393), '#skF_7') | ~r2_orders_2('#skF_3', B_393, '#skF_2'('#skF_3', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_2'('#skF_3', '#skF_6', '#skF_7'), u1_struct_0('#skF_3')) | ~m1_subset_1(B_393, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2644, c_2698])).
% 6.06/2.17  tff(c_2724, plain, (![B_393]: (r1_tarski(k3_orders_2('#skF_3', '#skF_6', B_393), '#skF_7') | ~r2_orders_2('#skF_3', B_393, '#skF_2'('#skF_3', '#skF_6', '#skF_7')) | ~m1_subset_1(B_393, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_2697, c_46, c_2714])).
% 6.06/2.17  tff(c_2990, plain, (![B_412]: (r1_tarski(k3_orders_2('#skF_3', '#skF_6', B_412), '#skF_7') | ~r2_orders_2('#skF_3', B_412, '#skF_2'('#skF_3', '#skF_6', '#skF_7')) | ~m1_subset_1(B_412, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_60, c_2724])).
% 6.06/2.17  tff(c_2993, plain, (r1_tarski(k3_orders_2('#skF_3', '#skF_6', '#skF_5'), '#skF_7') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_2696, c_2990])).
% 6.06/2.17  tff(c_2996, plain, (r1_tarski(k3_orders_2('#skF_3', '#skF_6', '#skF_5'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_2993])).
% 6.06/2.17  tff(c_2867, plain, (![B_403, A_404, D_405, C_406]: (r2_hidden(B_403, k3_orders_2(A_404, D_405, C_406)) | ~r2_hidden(B_403, D_405) | ~r2_orders_2(A_404, B_403, C_406) | ~m1_subset_1(D_405, k1_zfmisc_1(u1_struct_0(A_404))) | ~m1_subset_1(C_406, u1_struct_0(A_404)) | ~m1_subset_1(B_403, u1_struct_0(A_404)) | ~l1_orders_2(A_404) | ~v5_orders_2(A_404) | ~v4_orders_2(A_404) | ~v3_orders_2(A_404) | v2_struct_0(A_404))), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.06/2.17  tff(c_2873, plain, (![B_403, C_406]: (r2_hidden(B_403, k3_orders_2('#skF_3', '#skF_6', C_406)) | ~r2_hidden(B_403, '#skF_6') | ~r2_orders_2('#skF_3', B_403, C_406) | ~m1_subset_1(C_406, u1_struct_0('#skF_3')) | ~m1_subset_1(B_403, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_2867])).
% 6.06/2.17  tff(c_2884, plain, (![B_403, C_406]: (r2_hidden(B_403, k3_orders_2('#skF_3', '#skF_6', C_406)) | ~r2_hidden(B_403, '#skF_6') | ~r2_orders_2('#skF_3', B_403, C_406) | ~m1_subset_1(C_406, u1_struct_0('#skF_3')) | ~m1_subset_1(B_403, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_2873])).
% 6.06/2.17  tff(c_3078, plain, (![B_420, C_421]: (r2_hidden(B_420, k3_orders_2('#skF_3', '#skF_6', C_421)) | ~r2_hidden(B_420, '#skF_6') | ~r2_orders_2('#skF_3', B_420, C_421) | ~m1_subset_1(C_421, u1_struct_0('#skF_3')) | ~m1_subset_1(B_420, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_60, c_2884])).
% 6.06/2.17  tff(c_4040, plain, (![B_495, B_496, C_497]: (r2_hidden(B_495, B_496) | ~r1_tarski(k3_orders_2('#skF_3', '#skF_6', C_497), B_496) | ~r2_hidden(B_495, '#skF_6') | ~r2_orders_2('#skF_3', B_495, C_497) | ~m1_subset_1(C_497, u1_struct_0('#skF_3')) | ~m1_subset_1(B_495, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_3078, c_2])).
% 6.06/2.17  tff(c_4060, plain, (![B_495]: (r2_hidden(B_495, '#skF_7') | ~r2_hidden(B_495, '#skF_6') | ~r2_orders_2('#skF_3', B_495, '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1(B_495, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_2996, c_4040])).
% 6.06/2.17  tff(c_4092, plain, (![B_498]: (r2_hidden(B_498, '#skF_7') | ~r2_hidden(B_498, '#skF_6') | ~r2_orders_2('#skF_3', B_498, '#skF_5') | ~m1_subset_1(B_498, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_4060])).
% 6.06/2.17  tff(c_4111, plain, (r2_hidden('#skF_4', '#skF_7') | ~r2_hidden('#skF_4', '#skF_6') | ~r2_orders_2('#skF_3', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_50, c_4092])).
% 6.06/2.17  tff(c_4127, plain, (r2_hidden('#skF_4', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_4111])).
% 6.06/2.17  tff(c_4129, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_4127])).
% 6.06/2.17  tff(c_4130, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_2177])).
% 6.06/2.17  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.06/2.17  tff(c_100, plain, (![B_103]: (r2_hidden('#skF_5', B_103) | ~r1_tarski('#skF_7', B_103))), inference(resolution, [status(thm)], [c_38, c_90])).
% 6.06/2.17  tff(c_12, plain, (![B_11, A_10]: (~r1_tarski(B_11, A_10) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.06/2.17  tff(c_127, plain, (![B_108]: (~r1_tarski(B_108, '#skF_5') | ~r1_tarski('#skF_7', B_108))), inference(resolution, [status(thm)], [c_100, c_12])).
% 6.06/2.17  tff(c_135, plain, (~r1_tarski('#skF_7', k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_127])).
% 6.06/2.17  tff(c_4139, plain, (~r1_tarski('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_4130, c_135])).
% 6.06/2.17  tff(c_4144, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_4139])).
% 6.06/2.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.06/2.17  
% 6.06/2.17  Inference rules
% 6.06/2.17  ----------------------
% 6.06/2.17  #Ref     : 0
% 6.06/2.17  #Sup     : 874
% 6.06/2.17  #Fact    : 0
% 6.06/2.17  #Define  : 0
% 6.06/2.17  #Split   : 24
% 6.06/2.17  #Chain   : 0
% 6.06/2.17  #Close   : 0
% 6.06/2.17  
% 6.06/2.17  Ordering : KBO
% 6.06/2.17  
% 6.06/2.17  Simplification rules
% 6.06/2.17  ----------------------
% 6.06/2.17  #Subsume      : 381
% 6.06/2.17  #Demod        : 862
% 6.06/2.17  #Tautology    : 111
% 6.06/2.17  #SimpNegUnit  : 140
% 6.06/2.17  #BackRed      : 31
% 6.06/2.17  
% 6.06/2.17  #Partial instantiations: 0
% 6.06/2.17  #Strategies tried      : 1
% 6.06/2.17  
% 6.06/2.17  Timing (in seconds)
% 6.06/2.17  ----------------------
% 6.06/2.17  Preprocessing        : 0.34
% 6.06/2.17  Parsing              : 0.19
% 6.06/2.17  CNF conversion       : 0.03
% 6.06/2.17  Main loop            : 1.04
% 6.06/2.17  Inferencing          : 0.35
% 6.06/2.17  Reduction            : 0.33
% 6.06/2.17  Demodulation         : 0.23
% 6.06/2.17  BG Simplification    : 0.03
% 6.06/2.17  Subsumption          : 0.26
% 6.06/2.17  Abstraction          : 0.04
% 6.06/2.17  MUC search           : 0.00
% 6.06/2.17  Cooper               : 0.00
% 6.06/2.17  Total                : 1.44
% 6.06/2.17  Index Insertion      : 0.00
% 6.06/2.17  Index Deletion       : 0.00
% 6.06/2.17  Index Matching       : 0.00
% 6.06/2.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
