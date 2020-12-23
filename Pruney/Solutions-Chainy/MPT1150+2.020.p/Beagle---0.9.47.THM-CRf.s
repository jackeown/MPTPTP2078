%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:26 EST 2020

% Result     : Theorem 3.43s
% Output     : CNFRefutation 3.43s
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
%$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k4_tarski > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_orders_2)).

tff(f_98,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_63,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_orders_2)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).

tff(c_42,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_26,plain,(
    ! [A_27] :
      ( l1_struct_0(A_27)
      | ~ l1_orders_2(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_63,plain,(
    ! [A_44] :
      ( u1_struct_0(A_44) = k2_struct_0(A_44)
      | ~ l1_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_69,plain,(
    ! [A_46] :
      ( u1_struct_0(A_46) = k2_struct_0(A_46)
      | ~ l1_orders_2(A_46) ) ),
    inference(resolution,[status(thm)],[c_26,c_63])).

tff(c_73,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_69])).

tff(c_78,plain,(
    ! [A_47] :
      ( ~ v1_xboole_0(u1_struct_0(A_47))
      | ~ l1_struct_0(A_47)
      | v2_struct_0(A_47) ) ),
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
    ! [A_78,B_79] :
      ( k1_orders_2(A_78,B_79) = a_2_0_orders_2(A_78,B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_orders_2(A_78)
      | ~ v5_orders_2(A_78)
      | ~ v4_orders_2(A_78)
      | ~ v3_orders_2(A_78)
      | v2_struct_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_129,plain,(
    ! [B_79] :
      ( k1_orders_2('#skF_4',B_79) = a_2_0_orders_2('#skF_4',B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_126])).

tff(c_135,plain,(
    ! [B_79] :
      ( k1_orders_2('#skF_4',B_79) = a_2_0_orders_2('#skF_4',B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_129])).

tff(c_138,plain,(
    ! [B_80] :
      ( k1_orders_2('#skF_4',B_80) = a_2_0_orders_2('#skF_4',B_80)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
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
    ! [A_82,B_83,C_84] :
      ( '#skF_2'(A_82,B_83,C_84) = A_82
      | ~ r2_hidden(A_82,a_2_0_orders_2(B_83,C_84))
      | ~ m1_subset_1(C_84,k1_zfmisc_1(u1_struct_0(B_83)))
      | ~ l1_orders_2(B_83)
      | ~ v5_orders_2(B_83)
      | ~ v4_orders_2(B_83)
      | ~ v3_orders_2(B_83)
      | v2_struct_0(B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_210,plain,(
    ! [B_97,C_98] :
      ( '#skF_2'('#skF_1'(a_2_0_orders_2(B_97,C_98)),B_97,C_98) = '#skF_1'(a_2_0_orders_2(B_97,C_98))
      | ~ m1_subset_1(C_98,k1_zfmisc_1(u1_struct_0(B_97)))
      | ~ l1_orders_2(B_97)
      | ~ v5_orders_2(B_97)
      | ~ v4_orders_2(B_97)
      | ~ v3_orders_2(B_97)
      | v2_struct_0(B_97)
      | a_2_0_orders_2(B_97,C_98) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_164])).

tff(c_212,plain,(
    ! [C_98] :
      ( '#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4',C_98)),'#skF_4',C_98) = '#skF_1'(a_2_0_orders_2('#skF_4',C_98))
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | a_2_0_orders_2('#skF_4',C_98) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_210])).

tff(c_217,plain,(
    ! [C_98] :
      ( '#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4',C_98)),'#skF_4',C_98) = '#skF_1'(a_2_0_orders_2('#skF_4',C_98))
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | a_2_0_orders_2('#skF_4',C_98) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_212])).

tff(c_220,plain,(
    ! [C_99] :
      ( '#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4',C_99)),'#skF_4',C_99) = '#skF_1'(a_2_0_orders_2('#skF_4',C_99))
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | a_2_0_orders_2('#skF_4',C_99) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_217])).

tff(c_223,plain,
    ( '#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),'#skF_4',k2_struct_0('#skF_4')) = '#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')))
    | a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_51,c_220])).

tff(c_226,plain,(
    '#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),'#skF_4',k2_struct_0('#skF_4')) = '#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_223])).

tff(c_173,plain,(
    ! [A_85,B_86,C_87] :
      ( m1_subset_1('#skF_2'(A_85,B_86,C_87),u1_struct_0(B_86))
      | ~ r2_hidden(A_85,a_2_0_orders_2(B_86,C_87))
      | ~ m1_subset_1(C_87,k1_zfmisc_1(u1_struct_0(B_86)))
      | ~ l1_orders_2(B_86)
      | ~ v5_orders_2(B_86)
      | ~ v4_orders_2(B_86)
      | ~ v3_orders_2(B_86)
      | v2_struct_0(B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_178,plain,(
    ! [A_85,C_87] :
      ( m1_subset_1('#skF_2'(A_85,'#skF_4',C_87),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_85,a_2_0_orders_2('#skF_4',C_87))
      | ~ m1_subset_1(C_87,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_173])).

tff(c_181,plain,(
    ! [A_85,C_87] :
      ( m1_subset_1('#skF_2'(A_85,'#skF_4',C_87),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_85,a_2_0_orders_2('#skF_4',C_87))
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_73,c_178])).

tff(c_182,plain,(
    ! [A_85,C_87] :
      ( m1_subset_1('#skF_2'(A_85,'#skF_4',C_87),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_85,a_2_0_orders_2('#skF_4',C_87))
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
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
    ! [B_161,E_162,A_163,C_164] :
      ( r2_orders_2(B_161,E_162,'#skF_2'(A_163,B_161,C_164))
      | ~ r2_hidden(E_162,C_164)
      | ~ m1_subset_1(E_162,u1_struct_0(B_161))
      | ~ r2_hidden(A_163,a_2_0_orders_2(B_161,C_164))
      | ~ m1_subset_1(C_164,k1_zfmisc_1(u1_struct_0(B_161)))
      | ~ l1_orders_2(B_161)
      | ~ v5_orders_2(B_161)
      | ~ v4_orders_2(B_161)
      | ~ v3_orders_2(B_161)
      | v2_struct_0(B_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_812,plain,(
    ! [E_162,A_163,C_164] :
      ( r2_orders_2('#skF_4',E_162,'#skF_2'(A_163,'#skF_4',C_164))
      | ~ r2_hidden(E_162,C_164)
      | ~ m1_subset_1(E_162,u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_163,a_2_0_orders_2('#skF_4',C_164))
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_810])).

tff(c_817,plain,(
    ! [E_162,A_163,C_164] :
      ( r2_orders_2('#skF_4',E_162,'#skF_2'(A_163,'#skF_4',C_164))
      | ~ r2_hidden(E_162,C_164)
      | ~ m1_subset_1(E_162,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_163,a_2_0_orders_2('#skF_4',C_164))
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_73,c_812])).

tff(c_820,plain,(
    ! [E_165,A_166,C_167] :
      ( r2_orders_2('#skF_4',E_165,'#skF_2'(A_166,'#skF_4',C_167))
      | ~ r2_hidden(E_165,C_167)
      | ~ m1_subset_1(E_165,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_166,a_2_0_orders_2('#skF_4',C_167))
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_817])).

tff(c_825,plain,(
    ! [E_168,A_169] :
      ( r2_orders_2('#skF_4',E_168,'#skF_2'(A_169,'#skF_4',k2_struct_0('#skF_4')))
      | ~ r2_hidden(E_168,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_168,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_169,a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_51,c_820])).

tff(c_836,plain,(
    ! [E_168] :
      ( r2_orders_2('#skF_4',E_168,'#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))))
      | ~ r2_hidden(E_168,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_168,k2_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_825])).

tff(c_849,plain,(
    ! [E_170] :
      ( r2_orders_2('#skF_4',E_170,'#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))))
      | ~ r2_hidden(E_170,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_170,k2_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_266,c_836])).

tff(c_20,plain,(
    ! [A_17,C_23] :
      ( ~ r2_orders_2(A_17,C_23,C_23)
      | ~ m1_subset_1(C_23,u1_struct_0(A_17))
      | ~ l1_orders_2(A_17) ) ),
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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:34:51 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.43/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.43/1.51  
% 3.43/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.43/1.52  %$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k4_tarski > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3
% 3.43/1.52  
% 3.43/1.52  %Foreground sorts:
% 3.43/1.52  
% 3.43/1.52  
% 3.43/1.52  %Background operators:
% 3.43/1.52  
% 3.43/1.52  
% 3.43/1.52  %Foreground operators:
% 3.43/1.52  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.43/1.52  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.43/1.52  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 3.43/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.43/1.52  tff(a_2_0_orders_2, type, a_2_0_orders_2: ($i * $i) > $i).
% 3.43/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.43/1.52  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.43/1.52  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.43/1.52  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.43/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.43/1.52  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.43/1.52  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.43/1.52  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.43/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.43/1.52  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.43/1.52  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.43/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.43/1.52  tff('#skF_4', type, '#skF_4': $i).
% 3.43/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.43/1.52  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 3.43/1.52  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.43/1.52  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.43/1.52  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.43/1.52  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.43/1.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.43/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.43/1.52  
% 3.43/1.53  tff(f_139, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k1_orders_2(A, k2_struct_0(A)) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_orders_2)).
% 3.43/1.53  tff(f_98, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 3.43/1.53  tff(f_55, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.43/1.53  tff(f_63, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.43/1.53  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.43/1.53  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.43/1.53  tff(f_94, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_orders_2(A, B) = a_2_0_orders_2(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_orders_2)).
% 3.43/1.53  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 3.43/1.53  tff(f_125, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_0_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, E, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_0_orders_2)).
% 3.43/1.53  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.43/1.53  tff(f_78, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_orders_2)).
% 3.43/1.53  tff(c_42, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.43/1.53  tff(c_26, plain, (![A_27]: (l1_struct_0(A_27) | ~l1_orders_2(A_27))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.43/1.53  tff(c_50, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.43/1.53  tff(c_63, plain, (![A_44]: (u1_struct_0(A_44)=k2_struct_0(A_44) | ~l1_struct_0(A_44))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.43/1.53  tff(c_69, plain, (![A_46]: (u1_struct_0(A_46)=k2_struct_0(A_46) | ~l1_orders_2(A_46))), inference(resolution, [status(thm)], [c_26, c_63])).
% 3.43/1.53  tff(c_73, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_42, c_69])).
% 3.43/1.53  tff(c_78, plain, (![A_47]: (~v1_xboole_0(u1_struct_0(A_47)) | ~l1_struct_0(A_47) | v2_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.43/1.53  tff(c_81, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_73, c_78])).
% 3.43/1.53  tff(c_82, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_50, c_81])).
% 3.43/1.53  tff(c_83, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_82])).
% 3.43/1.53  tff(c_87, plain, (~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_26, c_83])).
% 3.43/1.53  tff(c_91, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_87])).
% 3.43/1.53  tff(c_92, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_82])).
% 3.43/1.53  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.43/1.53  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.43/1.53  tff(c_51, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 3.43/1.53  tff(c_48, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.43/1.53  tff(c_46, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.43/1.53  tff(c_44, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.43/1.53  tff(c_126, plain, (![A_78, B_79]: (k1_orders_2(A_78, B_79)=a_2_0_orders_2(A_78, B_79) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_orders_2(A_78) | ~v5_orders_2(A_78) | ~v4_orders_2(A_78) | ~v3_orders_2(A_78) | v2_struct_0(A_78))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.43/1.53  tff(c_129, plain, (![B_79]: (k1_orders_2('#skF_4', B_79)=a_2_0_orders_2('#skF_4', B_79) | ~m1_subset_1(B_79, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_73, c_126])).
% 3.43/1.53  tff(c_135, plain, (![B_79]: (k1_orders_2('#skF_4', B_79)=a_2_0_orders_2('#skF_4', B_79) | ~m1_subset_1(B_79, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_129])).
% 3.43/1.53  tff(c_138, plain, (![B_80]: (k1_orders_2('#skF_4', B_80)=a_2_0_orders_2('#skF_4', B_80) | ~m1_subset_1(B_80, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_135])).
% 3.43/1.53  tff(c_143, plain, (k1_orders_2('#skF_4', k2_struct_0('#skF_4'))=a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_51, c_138])).
% 3.43/1.53  tff(c_40, plain, (k1_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.43/1.53  tff(c_144, plain, (a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_143, c_40])).
% 3.43/1.53  tff(c_8, plain, (![A_5]: (r2_hidden('#skF_1'(A_5), A_5) | k1_xboole_0=A_5)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.43/1.53  tff(c_164, plain, (![A_82, B_83, C_84]: ('#skF_2'(A_82, B_83, C_84)=A_82 | ~r2_hidden(A_82, a_2_0_orders_2(B_83, C_84)) | ~m1_subset_1(C_84, k1_zfmisc_1(u1_struct_0(B_83))) | ~l1_orders_2(B_83) | ~v5_orders_2(B_83) | ~v4_orders_2(B_83) | ~v3_orders_2(B_83) | v2_struct_0(B_83))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.43/1.53  tff(c_210, plain, (![B_97, C_98]: ('#skF_2'('#skF_1'(a_2_0_orders_2(B_97, C_98)), B_97, C_98)='#skF_1'(a_2_0_orders_2(B_97, C_98)) | ~m1_subset_1(C_98, k1_zfmisc_1(u1_struct_0(B_97))) | ~l1_orders_2(B_97) | ~v5_orders_2(B_97) | ~v4_orders_2(B_97) | ~v3_orders_2(B_97) | v2_struct_0(B_97) | a_2_0_orders_2(B_97, C_98)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_164])).
% 3.43/1.53  tff(c_212, plain, (![C_98]: ('#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4', C_98)), '#skF_4', C_98)='#skF_1'(a_2_0_orders_2('#skF_4', C_98)) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | a_2_0_orders_2('#skF_4', C_98)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_73, c_210])).
% 3.43/1.53  tff(c_217, plain, (![C_98]: ('#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4', C_98)), '#skF_4', C_98)='#skF_1'(a_2_0_orders_2('#skF_4', C_98)) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | a_2_0_orders_2('#skF_4', C_98)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_212])).
% 3.43/1.53  tff(c_220, plain, (![C_99]: ('#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4', C_99)), '#skF_4', C_99)='#skF_1'(a_2_0_orders_2('#skF_4', C_99)) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_struct_0('#skF_4'))) | a_2_0_orders_2('#skF_4', C_99)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_50, c_217])).
% 3.43/1.53  tff(c_223, plain, ('#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), '#skF_4', k2_struct_0('#skF_4'))='#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))) | a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_51, c_220])).
% 3.43/1.53  tff(c_226, plain, ('#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), '#skF_4', k2_struct_0('#skF_4'))='#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_144, c_223])).
% 3.43/1.53  tff(c_173, plain, (![A_85, B_86, C_87]: (m1_subset_1('#skF_2'(A_85, B_86, C_87), u1_struct_0(B_86)) | ~r2_hidden(A_85, a_2_0_orders_2(B_86, C_87)) | ~m1_subset_1(C_87, k1_zfmisc_1(u1_struct_0(B_86))) | ~l1_orders_2(B_86) | ~v5_orders_2(B_86) | ~v4_orders_2(B_86) | ~v3_orders_2(B_86) | v2_struct_0(B_86))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.43/1.53  tff(c_178, plain, (![A_85, C_87]: (m1_subset_1('#skF_2'(A_85, '#skF_4', C_87), k2_struct_0('#skF_4')) | ~r2_hidden(A_85, a_2_0_orders_2('#skF_4', C_87)) | ~m1_subset_1(C_87, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_73, c_173])).
% 3.43/1.53  tff(c_181, plain, (![A_85, C_87]: (m1_subset_1('#skF_2'(A_85, '#skF_4', C_87), k2_struct_0('#skF_4')) | ~r2_hidden(A_85, a_2_0_orders_2('#skF_4', C_87)) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_73, c_178])).
% 3.43/1.53  tff(c_182, plain, (![A_85, C_87]: (m1_subset_1('#skF_2'(A_85, '#skF_4', C_87), k2_struct_0('#skF_4')) | ~r2_hidden(A_85, a_2_0_orders_2('#skF_4', C_87)) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_181])).
% 3.43/1.53  tff(c_240, plain, (m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_226, c_182])).
% 3.43/1.53  tff(c_247, plain, (m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_240])).
% 3.43/1.53  tff(c_252, plain, (~r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_247])).
% 3.43/1.53  tff(c_258, plain, (a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_252])).
% 3.43/1.53  tff(c_264, plain, $false, inference(negUnitSimplification, [status(thm)], [c_144, c_258])).
% 3.43/1.53  tff(c_265, plain, (m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_247])).
% 3.43/1.53  tff(c_6, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.43/1.53  tff(c_266, plain, (r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_247])).
% 3.43/1.53  tff(c_810, plain, (![B_161, E_162, A_163, C_164]: (r2_orders_2(B_161, E_162, '#skF_2'(A_163, B_161, C_164)) | ~r2_hidden(E_162, C_164) | ~m1_subset_1(E_162, u1_struct_0(B_161)) | ~r2_hidden(A_163, a_2_0_orders_2(B_161, C_164)) | ~m1_subset_1(C_164, k1_zfmisc_1(u1_struct_0(B_161))) | ~l1_orders_2(B_161) | ~v5_orders_2(B_161) | ~v4_orders_2(B_161) | ~v3_orders_2(B_161) | v2_struct_0(B_161))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.43/1.53  tff(c_812, plain, (![E_162, A_163, C_164]: (r2_orders_2('#skF_4', E_162, '#skF_2'(A_163, '#skF_4', C_164)) | ~r2_hidden(E_162, C_164) | ~m1_subset_1(E_162, u1_struct_0('#skF_4')) | ~r2_hidden(A_163, a_2_0_orders_2('#skF_4', C_164)) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_73, c_810])).
% 3.43/1.53  tff(c_817, plain, (![E_162, A_163, C_164]: (r2_orders_2('#skF_4', E_162, '#skF_2'(A_163, '#skF_4', C_164)) | ~r2_hidden(E_162, C_164) | ~m1_subset_1(E_162, k2_struct_0('#skF_4')) | ~r2_hidden(A_163, a_2_0_orders_2('#skF_4', C_164)) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_73, c_812])).
% 3.43/1.53  tff(c_820, plain, (![E_165, A_166, C_167]: (r2_orders_2('#skF_4', E_165, '#skF_2'(A_166, '#skF_4', C_167)) | ~r2_hidden(E_165, C_167) | ~m1_subset_1(E_165, k2_struct_0('#skF_4')) | ~r2_hidden(A_166, a_2_0_orders_2('#skF_4', C_167)) | ~m1_subset_1(C_167, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_817])).
% 3.43/1.53  tff(c_825, plain, (![E_168, A_169]: (r2_orders_2('#skF_4', E_168, '#skF_2'(A_169, '#skF_4', k2_struct_0('#skF_4'))) | ~r2_hidden(E_168, k2_struct_0('#skF_4')) | ~m1_subset_1(E_168, k2_struct_0('#skF_4')) | ~r2_hidden(A_169, a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_51, c_820])).
% 3.43/1.53  tff(c_836, plain, (![E_168]: (r2_orders_2('#skF_4', E_168, '#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')))) | ~r2_hidden(E_168, k2_struct_0('#skF_4')) | ~m1_subset_1(E_168, k2_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_226, c_825])).
% 3.43/1.53  tff(c_849, plain, (![E_170]: (r2_orders_2('#skF_4', E_170, '#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')))) | ~r2_hidden(E_170, k2_struct_0('#skF_4')) | ~m1_subset_1(E_170, k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_266, c_836])).
% 3.43/1.53  tff(c_20, plain, (![A_17, C_23]: (~r2_orders_2(A_17, C_23, C_23) | ~m1_subset_1(C_23, u1_struct_0(A_17)) | ~l1_orders_2(A_17))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.43/1.53  tff(c_857, plain, (~m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_849, c_20])).
% 3.43/1.53  tff(c_867, plain, (~r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_265, c_42, c_265, c_73, c_857])).
% 3.43/1.53  tff(c_891, plain, (v1_xboole_0(k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_6, c_867])).
% 3.43/1.53  tff(c_894, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_265, c_891])).
% 3.43/1.53  tff(c_896, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_894])).
% 3.43/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.43/1.53  
% 3.43/1.53  Inference rules
% 3.43/1.53  ----------------------
% 3.43/1.53  #Ref     : 0
% 3.43/1.53  #Sup     : 158
% 3.43/1.53  #Fact    : 0
% 3.43/1.53  #Define  : 0
% 3.43/1.53  #Split   : 5
% 3.43/1.53  #Chain   : 0
% 3.43/1.53  #Close   : 0
% 3.43/1.53  
% 3.43/1.53  Ordering : KBO
% 3.43/1.53  
% 3.43/1.53  Simplification rules
% 3.43/1.53  ----------------------
% 3.43/1.53  #Subsume      : 14
% 3.43/1.53  #Demod        : 393
% 3.43/1.53  #Tautology    : 56
% 3.43/1.53  #SimpNegUnit  : 60
% 3.43/1.53  #BackRed      : 18
% 3.43/1.53  
% 3.43/1.53  #Partial instantiations: 0
% 3.43/1.53  #Strategies tried      : 1
% 3.43/1.53  
% 3.43/1.53  Timing (in seconds)
% 3.43/1.53  ----------------------
% 3.58/1.54  Preprocessing        : 0.33
% 3.58/1.54  Parsing              : 0.18
% 3.58/1.54  CNF conversion       : 0.02
% 3.58/1.54  Main loop            : 0.42
% 3.58/1.54  Inferencing          : 0.16
% 3.58/1.54  Reduction            : 0.14
% 3.58/1.54  Demodulation         : 0.10
% 3.58/1.54  BG Simplification    : 0.02
% 3.58/1.54  Subsumption          : 0.07
% 3.58/1.54  Abstraction          : 0.03
% 3.58/1.54  MUC search           : 0.00
% 3.58/1.54  Cooper               : 0.00
% 3.58/1.54  Total                : 0.79
% 3.58/1.54  Index Insertion      : 0.00
% 3.58/1.54  Index Deletion       : 0.00
% 3.58/1.54  Index Matching       : 0.00
% 3.58/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
