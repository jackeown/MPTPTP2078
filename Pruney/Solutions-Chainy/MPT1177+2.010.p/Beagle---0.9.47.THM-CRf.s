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
% DateTime   : Thu Dec  3 10:19:56 EST 2020

% Result     : Theorem 3.33s
% Output     : CNFRefutation 3.74s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 337 expanded)
%              Number of leaves         :   37 ( 138 expanded)
%              Depth                    :   14
%              Number of atoms          :  315 (1388 expanded)
%              Number of equality atoms :   28 (  61 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(m1_orders_1,type,(
    m1_orders_1: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(k1_orders_1,type,(
    k1_orders_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(m1_orders_2,type,(
    m1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v6_orders_2,type,(
    v6_orders_2: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_39,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_192,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
           => ! [C] :
                ( m2_orders_2(C,A,B)
               => ! [D] :
                    ( m2_orders_2(D,A,B)
                   => ( r2_xboole_0(C,D)
                    <=> m1_orders_2(C,A,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_orders_2)).

tff(f_94,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_orders_2(C,A,B)
             => r1_tarski(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_orders_2)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ! [C] :
          ( m2_orders_2(C,A,B)
         => ( v6_orders_2(C,A)
            & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_orders_2)).

tff(f_120,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ~ ( B != k1_xboole_0
                & m1_orders_2(B,A,B) )
            & ~ ( ~ m1_orders_2(B,A,B)
                & B = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_orders_2)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_50,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => r2_xboole_0(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_55,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_139,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
         => ! [C] :
              ( m2_orders_2(C,A,B)
             => r2_hidden(k1_funct_1(B,u1_struct_0(A)),C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_orders_2)).

tff(f_167,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
         => ! [C] :
              ( m2_orders_2(C,A,B)
             => ! [D] :
                  ( m2_orders_2(D,A,B)
                 => ( C != D
                   => ( m1_orders_2(C,A,D)
                    <=> ~ m1_orders_2(D,A,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_orders_2)).

tff(c_10,plain,(
    ! [B_7] : ~ r2_xboole_0(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_52,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_50,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_48,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_46,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_42,plain,(
    m2_orders_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_44,plain,(
    m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_110,plain,(
    ! [A_73,B_74] :
      ( r2_xboole_0(A_73,B_74)
      | B_74 = A_73
      | ~ r1_tarski(A_73,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_56,plain,
    ( ~ m1_orders_2('#skF_4','#skF_2','#skF_5')
    | ~ r2_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_80,plain,(
    ~ r2_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_121,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_110,c_80])).

tff(c_127,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_121])).

tff(c_62,plain,
    ( r2_xboole_0('#skF_4','#skF_5')
    | m1_orders_2('#skF_4','#skF_2','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_81,plain,(
    m1_orders_2('#skF_4','#skF_2','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_62])).

tff(c_259,plain,(
    ! [C_97,B_98,A_99] :
      ( r1_tarski(C_97,B_98)
      | ~ m1_orders_2(C_97,A_99,B_98)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ l1_orders_2(A_99)
      | ~ v5_orders_2(A_99)
      | ~ v4_orders_2(A_99)
      | ~ v3_orders_2(A_99)
      | v2_struct_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_261,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_81,c_259])).

tff(c_264,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_261])).

tff(c_265,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_127,c_264])).

tff(c_40,plain,(
    m2_orders_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_286,plain,(
    ! [C_107,A_108,B_109] :
      ( m1_subset_1(C_107,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ m2_orders_2(C_107,A_108,B_109)
      | ~ m1_orders_1(B_109,k1_orders_1(u1_struct_0(A_108)))
      | ~ l1_orders_2(A_108)
      | ~ v5_orders_2(A_108)
      | ~ v4_orders_2(A_108)
      | ~ v3_orders_2(A_108)
      | v2_struct_0(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_290,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_286])).

tff(c_297,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_290])).

tff(c_299,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_265,c_297])).

tff(c_300,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_121])).

tff(c_302,plain,(
    m1_orders_2('#skF_4','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_300,c_81])).

tff(c_426,plain,(
    ! [B_128,A_129] :
      ( ~ m1_orders_2(B_128,A_129,B_128)
      | k1_xboole_0 = B_128
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ l1_orders_2(A_129)
      | ~ v5_orders_2(A_129)
      | ~ v4_orders_2(A_129)
      | ~ v3_orders_2(A_129)
      | v2_struct_0(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_428,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_302,c_426])).

tff(c_431,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_428])).

tff(c_432,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_431])).

tff(c_444,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_432])).

tff(c_470,plain,(
    ! [C_142,A_143,B_144] :
      ( m1_subset_1(C_142,k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ m2_orders_2(C_142,A_143,B_144)
      | ~ m1_orders_1(B_144,k1_orders_1(u1_struct_0(A_143)))
      | ~ l1_orders_2(A_143)
      | ~ v5_orders_2(A_143)
      | ~ v4_orders_2(A_143)
      | ~ v3_orders_2(A_143)
      | v2_struct_0(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_472,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_470])).

tff(c_475,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_472])).

tff(c_477,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_444,c_475])).

tff(c_478,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_432])).

tff(c_18,plain,(
    ! [B_9] : r1_tarski(B_9,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_20,plain,(
    ! [A_10] :
      ( r2_xboole_0(k1_xboole_0,A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_74,plain,(
    ! [A_65,B_66] :
      ( r1_tarski(A_65,B_66)
      | ~ r2_xboole_0(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_78,plain,(
    ! [A_10] :
      ( r1_tarski(k1_xboole_0,A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(resolution,[status(thm)],[c_20,c_74])).

tff(c_105,plain,(
    ! [A_71,B_72] :
      ( r2_hidden('#skF_1'(A_71,B_72),A_71)
      | r1_tarski(A_71,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_22,plain,(
    ! [B_12,A_11] :
      ( ~ r1_tarski(B_12,A_11)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_318,plain,(
    ! [A_112,B_113] :
      ( ~ r1_tarski(A_112,'#skF_1'(A_112,B_113))
      | r1_tarski(A_112,B_113) ) ),
    inference(resolution,[status(thm)],[c_105,c_22])).

tff(c_324,plain,(
    ! [B_114] :
      ( r1_tarski(k1_xboole_0,B_114)
      | '#skF_1'(k1_xboole_0,B_114) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_78,c_318])).

tff(c_109,plain,(
    ! [A_71,B_72] :
      ( ~ r1_tarski(A_71,'#skF_1'(A_71,B_72))
      | r1_tarski(A_71,B_72) ) ),
    inference(resolution,[status(thm)],[c_105,c_22])).

tff(c_343,plain,(
    ! [B_118] :
      ( r1_tarski(k1_xboole_0,B_118)
      | '#skF_1'(k1_xboole_0,'#skF_1'(k1_xboole_0,B_118)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_324,c_109])).

tff(c_352,plain,(
    ! [B_118] :
      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
      | r1_tarski(k1_xboole_0,'#skF_1'(k1_xboole_0,B_118))
      | r1_tarski(k1_xboole_0,B_118) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_109])).

tff(c_369,plain,(
    ! [B_119] :
      ( r1_tarski(k1_xboole_0,'#skF_1'(k1_xboole_0,B_119))
      | r1_tarski(k1_xboole_0,B_119) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_352])).

tff(c_378,plain,(
    ! [B_119] : r1_tarski(k1_xboole_0,B_119) ),
    inference(resolution,[status(thm)],[c_369,c_109])).

tff(c_482,plain,(
    ! [B_119] : r1_tarski('#skF_4',B_119) ),
    inference(demodulation,[status(thm),theory(equality)],[c_478,c_378])).

tff(c_573,plain,(
    ! [B_163,A_164,C_165] :
      ( r2_hidden(k1_funct_1(B_163,u1_struct_0(A_164)),C_165)
      | ~ m2_orders_2(C_165,A_164,B_163)
      | ~ m1_orders_1(B_163,k1_orders_1(u1_struct_0(A_164)))
      | ~ l1_orders_2(A_164)
      | ~ v5_orders_2(A_164)
      | ~ v4_orders_2(A_164)
      | ~ v3_orders_2(A_164)
      | v2_struct_0(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_597,plain,(
    ! [C_169,B_170,A_171] :
      ( ~ r1_tarski(C_169,k1_funct_1(B_170,u1_struct_0(A_171)))
      | ~ m2_orders_2(C_169,A_171,B_170)
      | ~ m1_orders_1(B_170,k1_orders_1(u1_struct_0(A_171)))
      | ~ l1_orders_2(A_171)
      | ~ v5_orders_2(A_171)
      | ~ v4_orders_2(A_171)
      | ~ v3_orders_2(A_171)
      | v2_struct_0(A_171) ) ),
    inference(resolution,[status(thm)],[c_573,c_22])).

tff(c_608,plain,(
    ! [A_172,B_173] :
      ( ~ m2_orders_2('#skF_4',A_172,B_173)
      | ~ m1_orders_1(B_173,k1_orders_1(u1_struct_0(A_172)))
      | ~ l1_orders_2(A_172)
      | ~ v5_orders_2(A_172)
      | ~ v4_orders_2(A_172)
      | ~ v3_orders_2(A_172)
      | v2_struct_0(A_172) ) ),
    inference(resolution,[status(thm)],[c_482,c_597])).

tff(c_611,plain,
    ( ~ m2_orders_2('#skF_4','#skF_2','#skF_3')
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_608])).

tff(c_614,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_42,c_611])).

tff(c_616,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_614])).

tff(c_618,plain,(
    r2_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ r2_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_622,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_618,c_12])).

tff(c_625,plain,(
    ! [B_174,A_175] :
      ( B_174 = A_175
      | ~ r1_tarski(B_174,A_175)
      | ~ r1_tarski(A_175,B_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_632,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_622,c_625])).

tff(c_638,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_632])).

tff(c_903,plain,(
    ! [C_230,A_231,B_232] :
      ( m1_subset_1(C_230,k1_zfmisc_1(u1_struct_0(A_231)))
      | ~ m2_orders_2(C_230,A_231,B_232)
      | ~ m1_orders_1(B_232,k1_orders_1(u1_struct_0(A_231)))
      | ~ l1_orders_2(A_231)
      | ~ v5_orders_2(A_231)
      | ~ v4_orders_2(A_231)
      | ~ v3_orders_2(A_231)
      | v2_struct_0(A_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_905,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_903])).

tff(c_910,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_905])).

tff(c_911,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_910])).

tff(c_617,plain,(
    ~ m1_orders_2('#skF_4','#skF_2','#skF_5') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_970,plain,(
    ! [C_251,A_252,D_253,B_254] :
      ( m1_orders_2(C_251,A_252,D_253)
      | m1_orders_2(D_253,A_252,C_251)
      | D_253 = C_251
      | ~ m2_orders_2(D_253,A_252,B_254)
      | ~ m2_orders_2(C_251,A_252,B_254)
      | ~ m1_orders_1(B_254,k1_orders_1(u1_struct_0(A_252)))
      | ~ l1_orders_2(A_252)
      | ~ v5_orders_2(A_252)
      | ~ v4_orders_2(A_252)
      | ~ v3_orders_2(A_252)
      | v2_struct_0(A_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_972,plain,(
    ! [C_251] :
      ( m1_orders_2(C_251,'#skF_2','#skF_4')
      | m1_orders_2('#skF_4','#skF_2',C_251)
      | C_251 = '#skF_4'
      | ~ m2_orders_2(C_251,'#skF_2','#skF_3')
      | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_42,c_970])).

tff(c_977,plain,(
    ! [C_251] :
      ( m1_orders_2(C_251,'#skF_2','#skF_4')
      | m1_orders_2('#skF_4','#skF_2',C_251)
      | C_251 = '#skF_4'
      | ~ m2_orders_2(C_251,'#skF_2','#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_972])).

tff(c_983,plain,(
    ! [C_255] :
      ( m1_orders_2(C_255,'#skF_2','#skF_4')
      | m1_orders_2('#skF_4','#skF_2',C_255)
      | C_255 = '#skF_4'
      | ~ m2_orders_2(C_255,'#skF_2','#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_977])).

tff(c_989,plain,
    ( m1_orders_2('#skF_5','#skF_2','#skF_4')
    | m1_orders_2('#skF_4','#skF_2','#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_983])).

tff(c_994,plain,
    ( m1_orders_2('#skF_5','#skF_2','#skF_4')
    | '#skF_5' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_617,c_989])).

tff(c_995,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_994])).

tff(c_1008,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_995,c_638])).

tff(c_1017,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1008])).

tff(c_1018,plain,(
    m1_orders_2('#skF_5','#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_994])).

tff(c_28,plain,(
    ! [C_23,B_21,A_17] :
      ( r1_tarski(C_23,B_21)
      | ~ m1_orders_2(C_23,A_17,B_21)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_orders_2(A_17)
      | ~ v5_orders_2(A_17)
      | ~ v4_orders_2(A_17)
      | ~ v3_orders_2(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1033,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_1018,c_28])).

tff(c_1036,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_911,c_1033])).

tff(c_1038,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_638,c_1036])).

tff(c_1039,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_632])).

tff(c_1043,plain,(
    r2_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1039,c_618])).

tff(c_1047,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_1043])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:39:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.33/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.62  
% 3.33/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.62  %$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.33/1.62  
% 3.33/1.62  %Foreground sorts:
% 3.33/1.62  
% 3.33/1.62  
% 3.33/1.62  %Background operators:
% 3.33/1.62  
% 3.33/1.62  
% 3.33/1.62  %Foreground operators:
% 3.33/1.62  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.33/1.62  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.33/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.33/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.33/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.33/1.62  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 3.33/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.33/1.62  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 3.33/1.62  tff('#skF_5', type, '#skF_5': $i).
% 3.33/1.62  tff('#skF_2', type, '#skF_2': $i).
% 3.33/1.62  tff('#skF_3', type, '#skF_3': $i).
% 3.33/1.62  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.33/1.62  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.33/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.33/1.62  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 3.33/1.62  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.33/1.62  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.33/1.62  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 3.33/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.33/1.62  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 3.33/1.62  tff('#skF_4', type, '#skF_4': $i).
% 3.33/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.33/1.62  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 3.33/1.62  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.33/1.62  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.33/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.33/1.62  
% 3.74/1.64  tff(f_39, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 3.74/1.64  tff(f_192, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (r2_xboole_0(C, D) <=> m1_orders_2(C, A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_orders_2)).
% 3.74/1.64  tff(f_94, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_orders_2)).
% 3.74/1.64  tff(f_75, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 3.74/1.64  tff(f_120, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (~(~(B = k1_xboole_0) & m1_orders_2(B, A, B)) & ~(~m1_orders_2(B, A, B) & (B = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_orders_2)).
% 3.74/1.64  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.74/1.64  tff(f_50, axiom, (![A]: (~(A = k1_xboole_0) => r2_xboole_0(k1_xboole_0, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_xboole_1)).
% 3.74/1.64  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.74/1.64  tff(f_55, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.74/1.64  tff(f_139, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => r2_hidden(k1_funct_1(B, u1_struct_0(A)), C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_orders_2)).
% 3.74/1.64  tff(f_167, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (~(C = D) => (m1_orders_2(C, A, D) <=> ~m1_orders_2(D, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_orders_2)).
% 3.74/1.64  tff(c_10, plain, (![B_7]: (~r2_xboole_0(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.74/1.64  tff(c_54, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_192])).
% 3.74/1.64  tff(c_52, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_192])).
% 3.74/1.64  tff(c_50, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_192])).
% 3.74/1.64  tff(c_48, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_192])).
% 3.74/1.64  tff(c_46, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_192])).
% 3.74/1.64  tff(c_42, plain, (m2_orders_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_192])).
% 3.74/1.64  tff(c_44, plain, (m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_192])).
% 3.74/1.64  tff(c_110, plain, (![A_73, B_74]: (r2_xboole_0(A_73, B_74) | B_74=A_73 | ~r1_tarski(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.74/1.64  tff(c_56, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_5') | ~r2_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_192])).
% 3.74/1.64  tff(c_80, plain, (~r2_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_56])).
% 3.74/1.64  tff(c_121, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_110, c_80])).
% 3.74/1.64  tff(c_127, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_121])).
% 3.74/1.64  tff(c_62, plain, (r2_xboole_0('#skF_4', '#skF_5') | m1_orders_2('#skF_4', '#skF_2', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_192])).
% 3.74/1.64  tff(c_81, plain, (m1_orders_2('#skF_4', '#skF_2', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_80, c_62])).
% 3.74/1.64  tff(c_259, plain, (![C_97, B_98, A_99]: (r1_tarski(C_97, B_98) | ~m1_orders_2(C_97, A_99, B_98) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0(A_99))) | ~l1_orders_2(A_99) | ~v5_orders_2(A_99) | ~v4_orders_2(A_99) | ~v3_orders_2(A_99) | v2_struct_0(A_99))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.74/1.64  tff(c_261, plain, (r1_tarski('#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_81, c_259])).
% 3.74/1.64  tff(c_264, plain, (r1_tarski('#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_261])).
% 3.74/1.64  tff(c_265, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_54, c_127, c_264])).
% 3.74/1.64  tff(c_40, plain, (m2_orders_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_192])).
% 3.74/1.64  tff(c_286, plain, (![C_107, A_108, B_109]: (m1_subset_1(C_107, k1_zfmisc_1(u1_struct_0(A_108))) | ~m2_orders_2(C_107, A_108, B_109) | ~m1_orders_1(B_109, k1_orders_1(u1_struct_0(A_108))) | ~l1_orders_2(A_108) | ~v5_orders_2(A_108) | ~v4_orders_2(A_108) | ~v3_orders_2(A_108) | v2_struct_0(A_108))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.74/1.64  tff(c_290, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_286])).
% 3.74/1.64  tff(c_297, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_290])).
% 3.74/1.64  tff(c_299, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_265, c_297])).
% 3.74/1.64  tff(c_300, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_121])).
% 3.74/1.64  tff(c_302, plain, (m1_orders_2('#skF_4', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_300, c_81])).
% 3.74/1.64  tff(c_426, plain, (![B_128, A_129]: (~m1_orders_2(B_128, A_129, B_128) | k1_xboole_0=B_128 | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0(A_129))) | ~l1_orders_2(A_129) | ~v5_orders_2(A_129) | ~v4_orders_2(A_129) | ~v3_orders_2(A_129) | v2_struct_0(A_129))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.74/1.64  tff(c_428, plain, (k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_302, c_426])).
% 3.74/1.64  tff(c_431, plain, (k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_428])).
% 3.74/1.64  tff(c_432, plain, (k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_54, c_431])).
% 3.74/1.64  tff(c_444, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_432])).
% 3.74/1.64  tff(c_470, plain, (![C_142, A_143, B_144]: (m1_subset_1(C_142, k1_zfmisc_1(u1_struct_0(A_143))) | ~m2_orders_2(C_142, A_143, B_144) | ~m1_orders_1(B_144, k1_orders_1(u1_struct_0(A_143))) | ~l1_orders_2(A_143) | ~v5_orders_2(A_143) | ~v4_orders_2(A_143) | ~v3_orders_2(A_143) | v2_struct_0(A_143))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.74/1.64  tff(c_472, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_470])).
% 3.74/1.64  tff(c_475, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_472])).
% 3.74/1.64  tff(c_477, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_444, c_475])).
% 3.74/1.64  tff(c_478, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_432])).
% 3.74/1.64  tff(c_18, plain, (![B_9]: (r1_tarski(B_9, B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.74/1.64  tff(c_20, plain, (![A_10]: (r2_xboole_0(k1_xboole_0, A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.74/1.64  tff(c_74, plain, (![A_65, B_66]: (r1_tarski(A_65, B_66) | ~r2_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.74/1.64  tff(c_78, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10) | k1_xboole_0=A_10)), inference(resolution, [status(thm)], [c_20, c_74])).
% 3.74/1.64  tff(c_105, plain, (![A_71, B_72]: (r2_hidden('#skF_1'(A_71, B_72), A_71) | r1_tarski(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.74/1.64  tff(c_22, plain, (![B_12, A_11]: (~r1_tarski(B_12, A_11) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.74/1.64  tff(c_318, plain, (![A_112, B_113]: (~r1_tarski(A_112, '#skF_1'(A_112, B_113)) | r1_tarski(A_112, B_113))), inference(resolution, [status(thm)], [c_105, c_22])).
% 3.74/1.64  tff(c_324, plain, (![B_114]: (r1_tarski(k1_xboole_0, B_114) | '#skF_1'(k1_xboole_0, B_114)=k1_xboole_0)), inference(resolution, [status(thm)], [c_78, c_318])).
% 3.74/1.64  tff(c_109, plain, (![A_71, B_72]: (~r1_tarski(A_71, '#skF_1'(A_71, B_72)) | r1_tarski(A_71, B_72))), inference(resolution, [status(thm)], [c_105, c_22])).
% 3.74/1.64  tff(c_343, plain, (![B_118]: (r1_tarski(k1_xboole_0, B_118) | '#skF_1'(k1_xboole_0, '#skF_1'(k1_xboole_0, B_118))=k1_xboole_0)), inference(resolution, [status(thm)], [c_324, c_109])).
% 3.74/1.64  tff(c_352, plain, (![B_118]: (~r1_tarski(k1_xboole_0, k1_xboole_0) | r1_tarski(k1_xboole_0, '#skF_1'(k1_xboole_0, B_118)) | r1_tarski(k1_xboole_0, B_118))), inference(superposition, [status(thm), theory('equality')], [c_343, c_109])).
% 3.74/1.64  tff(c_369, plain, (![B_119]: (r1_tarski(k1_xboole_0, '#skF_1'(k1_xboole_0, B_119)) | r1_tarski(k1_xboole_0, B_119))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_352])).
% 3.74/1.64  tff(c_378, plain, (![B_119]: (r1_tarski(k1_xboole_0, B_119))), inference(resolution, [status(thm)], [c_369, c_109])).
% 3.74/1.64  tff(c_482, plain, (![B_119]: (r1_tarski('#skF_4', B_119))), inference(demodulation, [status(thm), theory('equality')], [c_478, c_378])).
% 3.74/1.64  tff(c_573, plain, (![B_163, A_164, C_165]: (r2_hidden(k1_funct_1(B_163, u1_struct_0(A_164)), C_165) | ~m2_orders_2(C_165, A_164, B_163) | ~m1_orders_1(B_163, k1_orders_1(u1_struct_0(A_164))) | ~l1_orders_2(A_164) | ~v5_orders_2(A_164) | ~v4_orders_2(A_164) | ~v3_orders_2(A_164) | v2_struct_0(A_164))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.74/1.64  tff(c_597, plain, (![C_169, B_170, A_171]: (~r1_tarski(C_169, k1_funct_1(B_170, u1_struct_0(A_171))) | ~m2_orders_2(C_169, A_171, B_170) | ~m1_orders_1(B_170, k1_orders_1(u1_struct_0(A_171))) | ~l1_orders_2(A_171) | ~v5_orders_2(A_171) | ~v4_orders_2(A_171) | ~v3_orders_2(A_171) | v2_struct_0(A_171))), inference(resolution, [status(thm)], [c_573, c_22])).
% 3.74/1.64  tff(c_608, plain, (![A_172, B_173]: (~m2_orders_2('#skF_4', A_172, B_173) | ~m1_orders_1(B_173, k1_orders_1(u1_struct_0(A_172))) | ~l1_orders_2(A_172) | ~v5_orders_2(A_172) | ~v4_orders_2(A_172) | ~v3_orders_2(A_172) | v2_struct_0(A_172))), inference(resolution, [status(thm)], [c_482, c_597])).
% 3.74/1.64  tff(c_611, plain, (~m2_orders_2('#skF_4', '#skF_2', '#skF_3') | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_608])).
% 3.74/1.64  tff(c_614, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_42, c_611])).
% 3.74/1.64  tff(c_616, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_614])).
% 3.74/1.64  tff(c_618, plain, (r2_xboole_0('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_56])).
% 3.74/1.64  tff(c_12, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~r2_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.74/1.64  tff(c_622, plain, (r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_618, c_12])).
% 3.74/1.64  tff(c_625, plain, (![B_174, A_175]: (B_174=A_175 | ~r1_tarski(B_174, A_175) | ~r1_tarski(A_175, B_174))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.74/1.64  tff(c_632, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_622, c_625])).
% 3.74/1.64  tff(c_638, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_632])).
% 3.74/1.64  tff(c_903, plain, (![C_230, A_231, B_232]: (m1_subset_1(C_230, k1_zfmisc_1(u1_struct_0(A_231))) | ~m2_orders_2(C_230, A_231, B_232) | ~m1_orders_1(B_232, k1_orders_1(u1_struct_0(A_231))) | ~l1_orders_2(A_231) | ~v5_orders_2(A_231) | ~v4_orders_2(A_231) | ~v3_orders_2(A_231) | v2_struct_0(A_231))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.74/1.64  tff(c_905, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_903])).
% 3.74/1.64  tff(c_910, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_905])).
% 3.74/1.64  tff(c_911, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_54, c_910])).
% 3.74/1.64  tff(c_617, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_5')), inference(splitRight, [status(thm)], [c_56])).
% 3.74/1.64  tff(c_970, plain, (![C_251, A_252, D_253, B_254]: (m1_orders_2(C_251, A_252, D_253) | m1_orders_2(D_253, A_252, C_251) | D_253=C_251 | ~m2_orders_2(D_253, A_252, B_254) | ~m2_orders_2(C_251, A_252, B_254) | ~m1_orders_1(B_254, k1_orders_1(u1_struct_0(A_252))) | ~l1_orders_2(A_252) | ~v5_orders_2(A_252) | ~v4_orders_2(A_252) | ~v3_orders_2(A_252) | v2_struct_0(A_252))), inference(cnfTransformation, [status(thm)], [f_167])).
% 3.74/1.64  tff(c_972, plain, (![C_251]: (m1_orders_2(C_251, '#skF_2', '#skF_4') | m1_orders_2('#skF_4', '#skF_2', C_251) | C_251='#skF_4' | ~m2_orders_2(C_251, '#skF_2', '#skF_3') | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_42, c_970])).
% 3.74/1.64  tff(c_977, plain, (![C_251]: (m1_orders_2(C_251, '#skF_2', '#skF_4') | m1_orders_2('#skF_4', '#skF_2', C_251) | C_251='#skF_4' | ~m2_orders_2(C_251, '#skF_2', '#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_972])).
% 3.74/1.64  tff(c_983, plain, (![C_255]: (m1_orders_2(C_255, '#skF_2', '#skF_4') | m1_orders_2('#skF_4', '#skF_2', C_255) | C_255='#skF_4' | ~m2_orders_2(C_255, '#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_54, c_977])).
% 3.74/1.64  tff(c_989, plain, (m1_orders_2('#skF_5', '#skF_2', '#skF_4') | m1_orders_2('#skF_4', '#skF_2', '#skF_5') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_40, c_983])).
% 3.74/1.64  tff(c_994, plain, (m1_orders_2('#skF_5', '#skF_2', '#skF_4') | '#skF_5'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_617, c_989])).
% 3.74/1.64  tff(c_995, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_994])).
% 3.74/1.64  tff(c_1008, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_995, c_638])).
% 3.74/1.64  tff(c_1017, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_1008])).
% 3.74/1.64  tff(c_1018, plain, (m1_orders_2('#skF_5', '#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_994])).
% 3.74/1.64  tff(c_28, plain, (![C_23, B_21, A_17]: (r1_tarski(C_23, B_21) | ~m1_orders_2(C_23, A_17, B_21) | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_orders_2(A_17) | ~v5_orders_2(A_17) | ~v4_orders_2(A_17) | ~v3_orders_2(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.74/1.64  tff(c_1033, plain, (r1_tarski('#skF_5', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_1018, c_28])).
% 3.74/1.64  tff(c_1036, plain, (r1_tarski('#skF_5', '#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_911, c_1033])).
% 3.74/1.64  tff(c_1038, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_638, c_1036])).
% 3.74/1.64  tff(c_1039, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_632])).
% 3.74/1.64  tff(c_1043, plain, (r2_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1039, c_618])).
% 3.74/1.64  tff(c_1047, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_1043])).
% 3.74/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.74/1.64  
% 3.74/1.64  Inference rules
% 3.74/1.64  ----------------------
% 3.74/1.64  #Ref     : 0
% 3.74/1.64  #Sup     : 180
% 3.74/1.64  #Fact    : 0
% 3.74/1.64  #Define  : 0
% 3.74/1.64  #Split   : 6
% 3.74/1.64  #Chain   : 0
% 3.74/1.64  #Close   : 0
% 3.74/1.64  
% 3.74/1.64  Ordering : KBO
% 3.74/1.64  
% 3.74/1.64  Simplification rules
% 3.74/1.64  ----------------------
% 3.74/1.64  #Subsume      : 46
% 3.74/1.64  #Demod        : 254
% 3.74/1.64  #Tautology    : 94
% 3.74/1.64  #SimpNegUnit  : 28
% 3.74/1.64  #BackRed      : 29
% 3.74/1.64  
% 3.74/1.64  #Partial instantiations: 0
% 3.74/1.64  #Strategies tried      : 1
% 3.74/1.64  
% 3.74/1.64  Timing (in seconds)
% 3.74/1.64  ----------------------
% 3.74/1.65  Preprocessing        : 0.36
% 3.74/1.65  Parsing              : 0.19
% 3.74/1.65  CNF conversion       : 0.03
% 3.74/1.65  Main loop            : 0.49
% 3.74/1.65  Inferencing          : 0.18
% 3.74/1.65  Reduction            : 0.15
% 3.74/1.65  Demodulation         : 0.10
% 3.74/1.65  BG Simplification    : 0.03
% 3.74/1.65  Subsumption          : 0.11
% 3.74/1.65  Abstraction          : 0.02
% 3.74/1.65  MUC search           : 0.00
% 3.74/1.65  Cooper               : 0.00
% 3.74/1.65  Total                : 0.91
% 3.74/1.65  Index Insertion      : 0.00
% 3.74/1.65  Index Deletion       : 0.00
% 3.74/1.65  Index Matching       : 0.00
% 3.74/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
