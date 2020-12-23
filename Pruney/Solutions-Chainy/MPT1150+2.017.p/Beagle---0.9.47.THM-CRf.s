%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:26 EST 2020

% Result     : Theorem 3.28s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 741 expanded)
%              Number of leaves         :   37 ( 285 expanded)
%              Depth                    :   18
%              Number of atoms          :  223 (2177 expanded)
%              Number of equality atoms :   33 ( 447 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k3_mcart_1 > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff(k1_orders_2,type,(
    k1_orders_2: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(a_2_0_orders_2,type,(
    a_2_0_orders_2: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_139,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => k1_orders_2(A,k2_struct_0(A)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_orders_2)).

tff(f_98,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_63,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_94,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_orders_2(A,B) = a_2_0_orders_2(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_orders_2)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_125,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & v3_orders_2(B)
        & v4_orders_2(B)
        & v5_orders_2(B)
        & l1_orders_2(B)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B))) )
     => ( r2_hidden(A,a_2_0_orders_2(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & ! [E] :
                ( m1_subset_1(E,u1_struct_0(B))
               => ( r2_hidden(E,C)
                 => r2_orders_2(B,E,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_orders_2(A,B,C)
              <=> ( r1_orders_2(A,B,C)
                  & B != C ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).

tff(c_42,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_26,plain,(
    ! [A_31] :
      ( l1_struct_0(A_31)
      | ~ l1_orders_2(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_63,plain,(
    ! [A_48] :
      ( u1_struct_0(A_48) = k2_struct_0(A_48)
      | ~ l1_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_69,plain,(
    ! [A_50] :
      ( u1_struct_0(A_50) = k2_struct_0(A_50)
      | ~ l1_orders_2(A_50) ) ),
    inference(resolution,[status(thm)],[c_26,c_63])).

tff(c_73,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_69])).

tff(c_78,plain,(
    ! [A_51] :
      ( ~ v1_xboole_0(u1_struct_0(A_51))
      | ~ l1_struct_0(A_51)
      | v2_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_81,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_78])).

tff(c_82,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_81])).

tff(c_83,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_87,plain,(
    ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_83])).

tff(c_91,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_87])).

tff(c_92,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_51,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_48,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_46,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_44,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_126,plain,(
    ! [A_88,B_89] :
      ( k1_orders_2(A_88,B_89) = a_2_0_orders_2(A_88,B_89)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_orders_2(A_88)
      | ~ v5_orders_2(A_88)
      | ~ v4_orders_2(A_88)
      | ~ v3_orders_2(A_88)
      | v2_struct_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_129,plain,(
    ! [B_89] :
      ( k1_orders_2('#skF_4',B_89) = a_2_0_orders_2('#skF_4',B_89)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_126])).

tff(c_135,plain,(
    ! [B_89] :
      ( k1_orders_2('#skF_4',B_89) = a_2_0_orders_2('#skF_4',B_89)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_129])).

tff(c_138,plain,(
    ! [B_90] :
      ( k1_orders_2('#skF_4',B_90) = a_2_0_orders_2('#skF_4',B_90)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_135])).

tff(c_143,plain,(
    k1_orders_2('#skF_4',k2_struct_0('#skF_4')) = a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_51,c_138])).

tff(c_40,plain,(
    k1_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_144,plain,(
    a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_40])).

tff(c_8,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_1'(A_5),A_5)
      | k1_xboole_0 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_164,plain,(
    ! [A_92,B_93,C_94] :
      ( '#skF_2'(A_92,B_93,C_94) = A_92
      | ~ r2_hidden(A_92,a_2_0_orders_2(B_93,C_94))
      | ~ m1_subset_1(C_94,k1_zfmisc_1(u1_struct_0(B_93)))
      | ~ l1_orders_2(B_93)
      | ~ v5_orders_2(B_93)
      | ~ v4_orders_2(B_93)
      | ~ v3_orders_2(B_93)
      | v2_struct_0(B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_210,plain,(
    ! [B_107,C_108] :
      ( '#skF_2'('#skF_1'(a_2_0_orders_2(B_107,C_108)),B_107,C_108) = '#skF_1'(a_2_0_orders_2(B_107,C_108))
      | ~ m1_subset_1(C_108,k1_zfmisc_1(u1_struct_0(B_107)))
      | ~ l1_orders_2(B_107)
      | ~ v5_orders_2(B_107)
      | ~ v4_orders_2(B_107)
      | ~ v3_orders_2(B_107)
      | v2_struct_0(B_107)
      | a_2_0_orders_2(B_107,C_108) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_164])).

tff(c_212,plain,(
    ! [C_108] :
      ( '#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4',C_108)),'#skF_4',C_108) = '#skF_1'(a_2_0_orders_2('#skF_4',C_108))
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | a_2_0_orders_2('#skF_4',C_108) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_210])).

tff(c_217,plain,(
    ! [C_108] :
      ( '#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4',C_108)),'#skF_4',C_108) = '#skF_1'(a_2_0_orders_2('#skF_4',C_108))
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | a_2_0_orders_2('#skF_4',C_108) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_212])).

tff(c_220,plain,(
    ! [C_109] :
      ( '#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4',C_109)),'#skF_4',C_109) = '#skF_1'(a_2_0_orders_2('#skF_4',C_109))
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | a_2_0_orders_2('#skF_4',C_109) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_217])).

tff(c_223,plain,
    ( '#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),'#skF_4',k2_struct_0('#skF_4')) = '#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')))
    | a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_51,c_220])).

tff(c_226,plain,(
    '#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),'#skF_4',k2_struct_0('#skF_4')) = '#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_223])).

tff(c_173,plain,(
    ! [A_95,B_96,C_97] :
      ( m1_subset_1('#skF_2'(A_95,B_96,C_97),u1_struct_0(B_96))
      | ~ r2_hidden(A_95,a_2_0_orders_2(B_96,C_97))
      | ~ m1_subset_1(C_97,k1_zfmisc_1(u1_struct_0(B_96)))
      | ~ l1_orders_2(B_96)
      | ~ v5_orders_2(B_96)
      | ~ v4_orders_2(B_96)
      | ~ v3_orders_2(B_96)
      | v2_struct_0(B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_178,plain,(
    ! [A_95,C_97] :
      ( m1_subset_1('#skF_2'(A_95,'#skF_4',C_97),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_95,a_2_0_orders_2('#skF_4',C_97))
      | ~ m1_subset_1(C_97,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_173])).

tff(c_181,plain,(
    ! [A_95,C_97] :
      ( m1_subset_1('#skF_2'(A_95,'#skF_4',C_97),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_95,a_2_0_orders_2('#skF_4',C_97))
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_73,c_178])).

tff(c_182,plain,(
    ! [A_95,C_97] :
      ( m1_subset_1('#skF_2'(A_95,'#skF_4',C_97),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_95,a_2_0_orders_2('#skF_4',C_97))
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_181])).

tff(c_240,plain,
    ( m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4'))
    | ~ r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')))
    | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_182])).

tff(c_247,plain,
    ( m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4'))
    | ~ r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_240])).

tff(c_252,plain,(
    ~ r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_247])).

tff(c_258,plain,(
    a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_252])).

tff(c_264,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_258])).

tff(c_265,plain,(
    m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_247])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_266,plain,(
    r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_247])).

tff(c_810,plain,(
    ! [B_177,E_178,A_179,C_180] :
      ( r2_orders_2(B_177,E_178,'#skF_2'(A_179,B_177,C_180))
      | ~ r2_hidden(E_178,C_180)
      | ~ m1_subset_1(E_178,u1_struct_0(B_177))
      | ~ r2_hidden(A_179,a_2_0_orders_2(B_177,C_180))
      | ~ m1_subset_1(C_180,k1_zfmisc_1(u1_struct_0(B_177)))
      | ~ l1_orders_2(B_177)
      | ~ v5_orders_2(B_177)
      | ~ v4_orders_2(B_177)
      | ~ v3_orders_2(B_177)
      | v2_struct_0(B_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_812,plain,(
    ! [E_178,A_179,C_180] :
      ( r2_orders_2('#skF_4',E_178,'#skF_2'(A_179,'#skF_4',C_180))
      | ~ r2_hidden(E_178,C_180)
      | ~ m1_subset_1(E_178,u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_179,a_2_0_orders_2('#skF_4',C_180))
      | ~ m1_subset_1(C_180,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_810])).

tff(c_817,plain,(
    ! [E_178,A_179,C_180] :
      ( r2_orders_2('#skF_4',E_178,'#skF_2'(A_179,'#skF_4',C_180))
      | ~ r2_hidden(E_178,C_180)
      | ~ m1_subset_1(E_178,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_179,a_2_0_orders_2('#skF_4',C_180))
      | ~ m1_subset_1(C_180,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_73,c_812])).

tff(c_820,plain,(
    ! [E_181,A_182,C_183] :
      ( r2_orders_2('#skF_4',E_181,'#skF_2'(A_182,'#skF_4',C_183))
      | ~ r2_hidden(E_181,C_183)
      | ~ m1_subset_1(E_181,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_182,a_2_0_orders_2('#skF_4',C_183))
      | ~ m1_subset_1(C_183,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_817])).

tff(c_825,plain,(
    ! [E_184,A_185] :
      ( r2_orders_2('#skF_4',E_184,'#skF_2'(A_185,'#skF_4',k2_struct_0('#skF_4')))
      | ~ r2_hidden(E_184,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_184,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_185,a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_51,c_820])).

tff(c_836,plain,(
    ! [E_184] :
      ( r2_orders_2('#skF_4',E_184,'#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))))
      | ~ r2_hidden(E_184,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_184,k2_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_825])).

tff(c_849,plain,(
    ! [E_186] :
      ( r2_orders_2('#skF_4',E_186,'#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))))
      | ~ r2_hidden(E_186,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_186,k2_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_266,c_836])).

tff(c_20,plain,(
    ! [A_21,C_27] :
      ( ~ r2_orders_2(A_21,C_27,C_27)
      | ~ m1_subset_1(C_27,u1_struct_0(A_21))
      | ~ l1_orders_2(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_857,plain,
    ( ~ m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4')
    | ~ r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_849,c_20])).

tff(c_867,plain,(
    ~ r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_42,c_265,c_73,c_857])).

tff(c_891,plain,
    ( v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6,c_867])).

tff(c_894,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_891])).

tff(c_896,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_894])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:20:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.28/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.48  
% 3.28/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.48  %$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k3_mcart_1 > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3
% 3.28/1.48  
% 3.28/1.48  %Foreground sorts:
% 3.28/1.48  
% 3.28/1.48  
% 3.28/1.48  %Background operators:
% 3.28/1.48  
% 3.28/1.48  
% 3.28/1.48  %Foreground operators:
% 3.28/1.48  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.28/1.48  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.28/1.48  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 3.28/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.28/1.48  tff(a_2_0_orders_2, type, a_2_0_orders_2: ($i * $i) > $i).
% 3.28/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.28/1.48  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.28/1.48  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.28/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.28/1.48  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 3.28/1.48  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.28/1.48  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.28/1.48  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.28/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.28/1.48  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.28/1.48  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.28/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.28/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.28/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.28/1.48  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 3.28/1.48  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.28/1.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.28/1.48  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.28/1.48  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.28/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.28/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.28/1.48  
% 3.39/1.50  tff(f_139, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k1_orders_2(A, k2_struct_0(A)) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_orders_2)).
% 3.39/1.50  tff(f_98, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 3.39/1.50  tff(f_55, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.39/1.50  tff(f_63, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.39/1.50  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.39/1.50  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.39/1.50  tff(f_94, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_orders_2(A, B) = a_2_0_orders_2(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_orders_2)).
% 3.39/1.50  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 3.39/1.50  tff(f_125, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_0_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, E, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_0_orders_2)).
% 3.39/1.50  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.39/1.50  tff(f_78, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_orders_2)).
% 3.39/1.50  tff(c_42, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.39/1.50  tff(c_26, plain, (![A_31]: (l1_struct_0(A_31) | ~l1_orders_2(A_31))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.39/1.50  tff(c_50, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.39/1.50  tff(c_63, plain, (![A_48]: (u1_struct_0(A_48)=k2_struct_0(A_48) | ~l1_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.39/1.50  tff(c_69, plain, (![A_50]: (u1_struct_0(A_50)=k2_struct_0(A_50) | ~l1_orders_2(A_50))), inference(resolution, [status(thm)], [c_26, c_63])).
% 3.39/1.50  tff(c_73, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_42, c_69])).
% 3.39/1.50  tff(c_78, plain, (![A_51]: (~v1_xboole_0(u1_struct_0(A_51)) | ~l1_struct_0(A_51) | v2_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.39/1.50  tff(c_81, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_73, c_78])).
% 3.39/1.50  tff(c_82, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_50, c_81])).
% 3.39/1.50  tff(c_83, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_82])).
% 3.39/1.50  tff(c_87, plain, (~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_26, c_83])).
% 3.39/1.50  tff(c_91, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_87])).
% 3.39/1.50  tff(c_92, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_82])).
% 3.39/1.50  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.39/1.50  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.39/1.50  tff(c_51, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 3.39/1.50  tff(c_48, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.39/1.50  tff(c_46, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.39/1.50  tff(c_44, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.39/1.50  tff(c_126, plain, (![A_88, B_89]: (k1_orders_2(A_88, B_89)=a_2_0_orders_2(A_88, B_89) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_orders_2(A_88) | ~v5_orders_2(A_88) | ~v4_orders_2(A_88) | ~v3_orders_2(A_88) | v2_struct_0(A_88))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.39/1.50  tff(c_129, plain, (![B_89]: (k1_orders_2('#skF_4', B_89)=a_2_0_orders_2('#skF_4', B_89) | ~m1_subset_1(B_89, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_73, c_126])).
% 3.39/1.50  tff(c_135, plain, (![B_89]: (k1_orders_2('#skF_4', B_89)=a_2_0_orders_2('#skF_4', B_89) | ~m1_subset_1(B_89, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_129])).
% 3.39/1.50  tff(c_138, plain, (![B_90]: (k1_orders_2('#skF_4', B_90)=a_2_0_orders_2('#skF_4', B_90) | ~m1_subset_1(B_90, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_135])).
% 3.39/1.50  tff(c_143, plain, (k1_orders_2('#skF_4', k2_struct_0('#skF_4'))=a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_51, c_138])).
% 3.39/1.50  tff(c_40, plain, (k1_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.39/1.50  tff(c_144, plain, (a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_143, c_40])).
% 3.39/1.50  tff(c_8, plain, (![A_5]: (r2_hidden('#skF_1'(A_5), A_5) | k1_xboole_0=A_5)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.39/1.50  tff(c_164, plain, (![A_92, B_93, C_94]: ('#skF_2'(A_92, B_93, C_94)=A_92 | ~r2_hidden(A_92, a_2_0_orders_2(B_93, C_94)) | ~m1_subset_1(C_94, k1_zfmisc_1(u1_struct_0(B_93))) | ~l1_orders_2(B_93) | ~v5_orders_2(B_93) | ~v4_orders_2(B_93) | ~v3_orders_2(B_93) | v2_struct_0(B_93))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.39/1.50  tff(c_210, plain, (![B_107, C_108]: ('#skF_2'('#skF_1'(a_2_0_orders_2(B_107, C_108)), B_107, C_108)='#skF_1'(a_2_0_orders_2(B_107, C_108)) | ~m1_subset_1(C_108, k1_zfmisc_1(u1_struct_0(B_107))) | ~l1_orders_2(B_107) | ~v5_orders_2(B_107) | ~v4_orders_2(B_107) | ~v3_orders_2(B_107) | v2_struct_0(B_107) | a_2_0_orders_2(B_107, C_108)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_164])).
% 3.39/1.50  tff(c_212, plain, (![C_108]: ('#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4', C_108)), '#skF_4', C_108)='#skF_1'(a_2_0_orders_2('#skF_4', C_108)) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | a_2_0_orders_2('#skF_4', C_108)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_73, c_210])).
% 3.39/1.50  tff(c_217, plain, (![C_108]: ('#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4', C_108)), '#skF_4', C_108)='#skF_1'(a_2_0_orders_2('#skF_4', C_108)) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | a_2_0_orders_2('#skF_4', C_108)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_212])).
% 3.39/1.50  tff(c_220, plain, (![C_109]: ('#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4', C_109)), '#skF_4', C_109)='#skF_1'(a_2_0_orders_2('#skF_4', C_109)) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_struct_0('#skF_4'))) | a_2_0_orders_2('#skF_4', C_109)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_50, c_217])).
% 3.39/1.50  tff(c_223, plain, ('#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), '#skF_4', k2_struct_0('#skF_4'))='#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))) | a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_51, c_220])).
% 3.39/1.50  tff(c_226, plain, ('#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), '#skF_4', k2_struct_0('#skF_4'))='#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_144, c_223])).
% 3.39/1.50  tff(c_173, plain, (![A_95, B_96, C_97]: (m1_subset_1('#skF_2'(A_95, B_96, C_97), u1_struct_0(B_96)) | ~r2_hidden(A_95, a_2_0_orders_2(B_96, C_97)) | ~m1_subset_1(C_97, k1_zfmisc_1(u1_struct_0(B_96))) | ~l1_orders_2(B_96) | ~v5_orders_2(B_96) | ~v4_orders_2(B_96) | ~v3_orders_2(B_96) | v2_struct_0(B_96))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.39/1.50  tff(c_178, plain, (![A_95, C_97]: (m1_subset_1('#skF_2'(A_95, '#skF_4', C_97), k2_struct_0('#skF_4')) | ~r2_hidden(A_95, a_2_0_orders_2('#skF_4', C_97)) | ~m1_subset_1(C_97, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_73, c_173])).
% 3.39/1.50  tff(c_181, plain, (![A_95, C_97]: (m1_subset_1('#skF_2'(A_95, '#skF_4', C_97), k2_struct_0('#skF_4')) | ~r2_hidden(A_95, a_2_0_orders_2('#skF_4', C_97)) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_73, c_178])).
% 3.39/1.50  tff(c_182, plain, (![A_95, C_97]: (m1_subset_1('#skF_2'(A_95, '#skF_4', C_97), k2_struct_0('#skF_4')) | ~r2_hidden(A_95, a_2_0_orders_2('#skF_4', C_97)) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_181])).
% 3.39/1.50  tff(c_240, plain, (m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_226, c_182])).
% 3.39/1.50  tff(c_247, plain, (m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_240])).
% 3.39/1.50  tff(c_252, plain, (~r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_247])).
% 3.39/1.50  tff(c_258, plain, (a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_252])).
% 3.39/1.50  tff(c_264, plain, $false, inference(negUnitSimplification, [status(thm)], [c_144, c_258])).
% 3.39/1.50  tff(c_265, plain, (m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_247])).
% 3.39/1.50  tff(c_6, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.39/1.50  tff(c_266, plain, (r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_247])).
% 3.39/1.50  tff(c_810, plain, (![B_177, E_178, A_179, C_180]: (r2_orders_2(B_177, E_178, '#skF_2'(A_179, B_177, C_180)) | ~r2_hidden(E_178, C_180) | ~m1_subset_1(E_178, u1_struct_0(B_177)) | ~r2_hidden(A_179, a_2_0_orders_2(B_177, C_180)) | ~m1_subset_1(C_180, k1_zfmisc_1(u1_struct_0(B_177))) | ~l1_orders_2(B_177) | ~v5_orders_2(B_177) | ~v4_orders_2(B_177) | ~v3_orders_2(B_177) | v2_struct_0(B_177))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.39/1.50  tff(c_812, plain, (![E_178, A_179, C_180]: (r2_orders_2('#skF_4', E_178, '#skF_2'(A_179, '#skF_4', C_180)) | ~r2_hidden(E_178, C_180) | ~m1_subset_1(E_178, u1_struct_0('#skF_4')) | ~r2_hidden(A_179, a_2_0_orders_2('#skF_4', C_180)) | ~m1_subset_1(C_180, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_73, c_810])).
% 3.39/1.50  tff(c_817, plain, (![E_178, A_179, C_180]: (r2_orders_2('#skF_4', E_178, '#skF_2'(A_179, '#skF_4', C_180)) | ~r2_hidden(E_178, C_180) | ~m1_subset_1(E_178, k2_struct_0('#skF_4')) | ~r2_hidden(A_179, a_2_0_orders_2('#skF_4', C_180)) | ~m1_subset_1(C_180, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_73, c_812])).
% 3.39/1.50  tff(c_820, plain, (![E_181, A_182, C_183]: (r2_orders_2('#skF_4', E_181, '#skF_2'(A_182, '#skF_4', C_183)) | ~r2_hidden(E_181, C_183) | ~m1_subset_1(E_181, k2_struct_0('#skF_4')) | ~r2_hidden(A_182, a_2_0_orders_2('#skF_4', C_183)) | ~m1_subset_1(C_183, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_817])).
% 3.39/1.50  tff(c_825, plain, (![E_184, A_185]: (r2_orders_2('#skF_4', E_184, '#skF_2'(A_185, '#skF_4', k2_struct_0('#skF_4'))) | ~r2_hidden(E_184, k2_struct_0('#skF_4')) | ~m1_subset_1(E_184, k2_struct_0('#skF_4')) | ~r2_hidden(A_185, a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_51, c_820])).
% 3.39/1.50  tff(c_836, plain, (![E_184]: (r2_orders_2('#skF_4', E_184, '#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')))) | ~r2_hidden(E_184, k2_struct_0('#skF_4')) | ~m1_subset_1(E_184, k2_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_226, c_825])).
% 3.39/1.50  tff(c_849, plain, (![E_186]: (r2_orders_2('#skF_4', E_186, '#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')))) | ~r2_hidden(E_186, k2_struct_0('#skF_4')) | ~m1_subset_1(E_186, k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_266, c_836])).
% 3.39/1.50  tff(c_20, plain, (![A_21, C_27]: (~r2_orders_2(A_21, C_27, C_27) | ~m1_subset_1(C_27, u1_struct_0(A_21)) | ~l1_orders_2(A_21))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.39/1.50  tff(c_857, plain, (~m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_849, c_20])).
% 3.39/1.50  tff(c_867, plain, (~r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_265, c_42, c_265, c_73, c_857])).
% 3.39/1.50  tff(c_891, plain, (v1_xboole_0(k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_6, c_867])).
% 3.39/1.50  tff(c_894, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_265, c_891])).
% 3.39/1.50  tff(c_896, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_894])).
% 3.39/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.39/1.50  
% 3.39/1.50  Inference rules
% 3.39/1.50  ----------------------
% 3.39/1.50  #Ref     : 0
% 3.39/1.50  #Sup     : 158
% 3.39/1.50  #Fact    : 0
% 3.39/1.50  #Define  : 0
% 3.39/1.50  #Split   : 5
% 3.39/1.50  #Chain   : 0
% 3.39/1.50  #Close   : 0
% 3.39/1.50  
% 3.39/1.50  Ordering : KBO
% 3.39/1.50  
% 3.39/1.50  Simplification rules
% 3.39/1.50  ----------------------
% 3.39/1.50  #Subsume      : 14
% 3.39/1.50  #Demod        : 393
% 3.39/1.50  #Tautology    : 56
% 3.39/1.50  #SimpNegUnit  : 60
% 3.39/1.50  #BackRed      : 18
% 3.39/1.50  
% 3.39/1.50  #Partial instantiations: 0
% 3.39/1.50  #Strategies tried      : 1
% 3.39/1.50  
% 3.39/1.50  Timing (in seconds)
% 3.39/1.50  ----------------------
% 3.39/1.50  Preprocessing        : 0.31
% 3.39/1.50  Parsing              : 0.16
% 3.39/1.50  CNF conversion       : 0.02
% 3.39/1.50  Main loop            : 0.42
% 3.39/1.50  Inferencing          : 0.15
% 3.39/1.51  Reduction            : 0.14
% 3.39/1.51  Demodulation         : 0.10
% 3.39/1.51  BG Simplification    : 0.02
% 3.39/1.51  Subsumption          : 0.07
% 3.39/1.51  Abstraction          : 0.03
% 3.39/1.51  MUC search           : 0.00
% 3.39/1.51  Cooper               : 0.00
% 3.39/1.51  Total                : 0.77
% 3.39/1.51  Index Insertion      : 0.00
% 3.39/1.51  Index Deletion       : 0.00
% 3.39/1.51  Index Matching       : 0.00
% 3.39/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
