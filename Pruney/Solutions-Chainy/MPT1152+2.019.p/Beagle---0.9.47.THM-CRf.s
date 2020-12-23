%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:30 EST 2020

% Result     : Theorem 3.26s
% Output     : CNFRefutation 3.44s
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
%$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k4_tarski > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(a_2_1_orders_2,type,(
    a_2_1_orders_2: ( $i * $i ) > $i )).

tff(k2_orders_2,type,(
    k2_orders_2: ( $i * $i ) > $i )).

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
       => k2_orders_2(A,k2_struct_0(A)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_orders_2)).

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
         => k2_orders_2(A,B) = a_2_1_orders_2(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_orders_2)).

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
     => ( r2_hidden(A,a_2_1_orders_2(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & ! [E] :
                ( m1_subset_1(E,u1_struct_0(B))
               => ( r2_hidden(E,C)
                 => r2_orders_2(B,D,E) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

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
      ( k2_orders_2(A_78,B_79) = a_2_1_orders_2(A_78,B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_orders_2(A_78)
      | ~ v5_orders_2(A_78)
      | ~ v4_orders_2(A_78)
      | ~ v3_orders_2(A_78)
      | v2_struct_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_129,plain,(
    ! [B_79] :
      ( k2_orders_2('#skF_4',B_79) = a_2_1_orders_2('#skF_4',B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_126])).

tff(c_135,plain,(
    ! [B_79] :
      ( k2_orders_2('#skF_4',B_79) = a_2_1_orders_2('#skF_4',B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_129])).

tff(c_138,plain,(
    ! [B_80] :
      ( k2_orders_2('#skF_4',B_80) = a_2_1_orders_2('#skF_4',B_80)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_135])).

tff(c_143,plain,(
    k2_orders_2('#skF_4',k2_struct_0('#skF_4')) = a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_51,c_138])).

tff(c_40,plain,(
    k2_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_144,plain,(
    a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_40])).

tff(c_8,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_1'(A_5),A_5)
      | k1_xboole_0 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_164,plain,(
    ! [A_82,B_83,C_84] :
      ( '#skF_2'(A_82,B_83,C_84) = A_82
      | ~ r2_hidden(A_82,a_2_1_orders_2(B_83,C_84))
      | ~ m1_subset_1(C_84,k1_zfmisc_1(u1_struct_0(B_83)))
      | ~ l1_orders_2(B_83)
      | ~ v5_orders_2(B_83)
      | ~ v4_orders_2(B_83)
      | ~ v3_orders_2(B_83)
      | v2_struct_0(B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_210,plain,(
    ! [B_97,C_98] :
      ( '#skF_2'('#skF_1'(a_2_1_orders_2(B_97,C_98)),B_97,C_98) = '#skF_1'(a_2_1_orders_2(B_97,C_98))
      | ~ m1_subset_1(C_98,k1_zfmisc_1(u1_struct_0(B_97)))
      | ~ l1_orders_2(B_97)
      | ~ v5_orders_2(B_97)
      | ~ v4_orders_2(B_97)
      | ~ v3_orders_2(B_97)
      | v2_struct_0(B_97)
      | a_2_1_orders_2(B_97,C_98) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_164])).

tff(c_212,plain,(
    ! [C_98] :
      ( '#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4',C_98)),'#skF_4',C_98) = '#skF_1'(a_2_1_orders_2('#skF_4',C_98))
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | a_2_1_orders_2('#skF_4',C_98) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_210])).

tff(c_217,plain,(
    ! [C_98] :
      ( '#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4',C_98)),'#skF_4',C_98) = '#skF_1'(a_2_1_orders_2('#skF_4',C_98))
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | a_2_1_orders_2('#skF_4',C_98) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_212])).

tff(c_220,plain,(
    ! [C_99] :
      ( '#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4',C_99)),'#skF_4',C_99) = '#skF_1'(a_2_1_orders_2('#skF_4',C_99))
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | a_2_1_orders_2('#skF_4',C_99) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_217])).

tff(c_223,plain,
    ( '#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),'#skF_4',k2_struct_0('#skF_4')) = '#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
    | a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_51,c_220])).

tff(c_226,plain,(
    '#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),'#skF_4',k2_struct_0('#skF_4')) = '#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_223])).

tff(c_173,plain,(
    ! [A_85,B_86,C_87] :
      ( m1_subset_1('#skF_2'(A_85,B_86,C_87),u1_struct_0(B_86))
      | ~ r2_hidden(A_85,a_2_1_orders_2(B_86,C_87))
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
      | ~ r2_hidden(A_85,a_2_1_orders_2('#skF_4',C_87))
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
      | ~ r2_hidden(A_85,a_2_1_orders_2('#skF_4',C_87))
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_73,c_178])).

tff(c_182,plain,(
    ! [A_85,C_87] :
      ( m1_subset_1('#skF_2'(A_85,'#skF_4',C_87),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_85,a_2_1_orders_2('#skF_4',C_87))
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_181])).

tff(c_240,plain,
    ( m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4'))
    | ~ r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
    | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_182])).

tff(c_247,plain,
    ( m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4'))
    | ~ r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_240])).

tff(c_252,plain,(
    ~ r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_247])).

tff(c_258,plain,(
    a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_252])).

tff(c_264,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_258])).

tff(c_265,plain,(
    m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_247])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_266,plain,(
    r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_247])).

tff(c_800,plain,(
    ! [B_163,A_164,C_165,E_166] :
      ( r2_orders_2(B_163,'#skF_2'(A_164,B_163,C_165),E_166)
      | ~ r2_hidden(E_166,C_165)
      | ~ m1_subset_1(E_166,u1_struct_0(B_163))
      | ~ r2_hidden(A_164,a_2_1_orders_2(B_163,C_165))
      | ~ m1_subset_1(C_165,k1_zfmisc_1(u1_struct_0(B_163)))
      | ~ l1_orders_2(B_163)
      | ~ v5_orders_2(B_163)
      | ~ v4_orders_2(B_163)
      | ~ v3_orders_2(B_163)
      | v2_struct_0(B_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_802,plain,(
    ! [A_164,C_165,E_166] :
      ( r2_orders_2('#skF_4','#skF_2'(A_164,'#skF_4',C_165),E_166)
      | ~ r2_hidden(E_166,C_165)
      | ~ m1_subset_1(E_166,u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_164,a_2_1_orders_2('#skF_4',C_165))
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_800])).

tff(c_807,plain,(
    ! [A_164,C_165,E_166] :
      ( r2_orders_2('#skF_4','#skF_2'(A_164,'#skF_4',C_165),E_166)
      | ~ r2_hidden(E_166,C_165)
      | ~ m1_subset_1(E_166,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_164,a_2_1_orders_2('#skF_4',C_165))
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_73,c_802])).

tff(c_810,plain,(
    ! [A_167,C_168,E_169] :
      ( r2_orders_2('#skF_4','#skF_2'(A_167,'#skF_4',C_168),E_169)
      | ~ r2_hidden(E_169,C_168)
      | ~ m1_subset_1(E_169,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_167,a_2_1_orders_2('#skF_4',C_168))
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_807])).

tff(c_815,plain,(
    ! [A_170,E_171] :
      ( r2_orders_2('#skF_4','#skF_2'(A_170,'#skF_4',k2_struct_0('#skF_4')),E_171)
      | ~ r2_hidden(E_171,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_171,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_170,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_51,c_810])).

tff(c_826,plain,(
    ! [E_171] :
      ( r2_orders_2('#skF_4','#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),E_171)
      | ~ r2_hidden(E_171,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_171,k2_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_815])).

tff(c_839,plain,(
    ! [E_172] :
      ( r2_orders_2('#skF_4','#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),E_172)
      | ~ r2_hidden(E_172,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_172,k2_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_266,c_826])).

tff(c_20,plain,(
    ! [A_17,C_23] :
      ( ~ r2_orders_2(A_17,C_23,C_23)
      | ~ m1_subset_1(C_23,u1_struct_0(A_17))
      | ~ l1_orders_2(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_847,plain,
    ( ~ m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4')
    | ~ r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_839,c_20])).

tff(c_857,plain,(
    ~ r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_42,c_265,c_73,c_847])).

tff(c_881,plain,
    ( v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6,c_857])).

tff(c_884,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_881])).

tff(c_886,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_884])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:47:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.26/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.51  
% 3.44/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.51  %$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k4_tarski > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3
% 3.44/1.51  
% 3.44/1.51  %Foreground sorts:
% 3.44/1.51  
% 3.44/1.51  
% 3.44/1.51  %Background operators:
% 3.44/1.51  
% 3.44/1.51  
% 3.44/1.51  %Foreground operators:
% 3.44/1.51  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.44/1.51  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.44/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.44/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.44/1.51  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.44/1.51  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.44/1.51  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.44/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.44/1.51  tff(a_2_1_orders_2, type, a_2_1_orders_2: ($i * $i) > $i).
% 3.44/1.51  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 3.44/1.51  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.44/1.51  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.44/1.51  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.44/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.44/1.51  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.44/1.51  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.44/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.44/1.51  tff('#skF_4', type, '#skF_4': $i).
% 3.44/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.44/1.51  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 3.44/1.51  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.44/1.51  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.44/1.51  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.44/1.51  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.44/1.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.44/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.44/1.51  
% 3.44/1.53  tff(f_139, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k2_orders_2(A, k2_struct_0(A)) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_orders_2)).
% 3.44/1.53  tff(f_98, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 3.44/1.53  tff(f_55, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.44/1.53  tff(f_63, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.44/1.53  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.44/1.53  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.44/1.53  tff(f_94, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_orders_2(A, B) = a_2_1_orders_2(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_orders_2)).
% 3.44/1.53  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 3.44/1.53  tff(f_125, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_1_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, D, E))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_1_orders_2)).
% 3.44/1.53  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.44/1.53  tff(f_78, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_orders_2)).
% 3.44/1.53  tff(c_42, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.44/1.53  tff(c_26, plain, (![A_27]: (l1_struct_0(A_27) | ~l1_orders_2(A_27))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.44/1.53  tff(c_50, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.44/1.53  tff(c_63, plain, (![A_44]: (u1_struct_0(A_44)=k2_struct_0(A_44) | ~l1_struct_0(A_44))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.44/1.53  tff(c_69, plain, (![A_46]: (u1_struct_0(A_46)=k2_struct_0(A_46) | ~l1_orders_2(A_46))), inference(resolution, [status(thm)], [c_26, c_63])).
% 3.44/1.53  tff(c_73, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_42, c_69])).
% 3.44/1.53  tff(c_78, plain, (![A_47]: (~v1_xboole_0(u1_struct_0(A_47)) | ~l1_struct_0(A_47) | v2_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.44/1.53  tff(c_81, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_73, c_78])).
% 3.44/1.53  tff(c_82, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_50, c_81])).
% 3.44/1.53  tff(c_83, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_82])).
% 3.44/1.53  tff(c_87, plain, (~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_26, c_83])).
% 3.44/1.53  tff(c_91, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_87])).
% 3.44/1.53  tff(c_92, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_82])).
% 3.44/1.53  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.44/1.53  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.44/1.53  tff(c_51, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 3.44/1.53  tff(c_48, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.44/1.53  tff(c_46, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.44/1.53  tff(c_44, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.44/1.53  tff(c_126, plain, (![A_78, B_79]: (k2_orders_2(A_78, B_79)=a_2_1_orders_2(A_78, B_79) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_orders_2(A_78) | ~v5_orders_2(A_78) | ~v4_orders_2(A_78) | ~v3_orders_2(A_78) | v2_struct_0(A_78))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.44/1.53  tff(c_129, plain, (![B_79]: (k2_orders_2('#skF_4', B_79)=a_2_1_orders_2('#skF_4', B_79) | ~m1_subset_1(B_79, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_73, c_126])).
% 3.44/1.53  tff(c_135, plain, (![B_79]: (k2_orders_2('#skF_4', B_79)=a_2_1_orders_2('#skF_4', B_79) | ~m1_subset_1(B_79, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_129])).
% 3.44/1.53  tff(c_138, plain, (![B_80]: (k2_orders_2('#skF_4', B_80)=a_2_1_orders_2('#skF_4', B_80) | ~m1_subset_1(B_80, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_135])).
% 3.44/1.53  tff(c_143, plain, (k2_orders_2('#skF_4', k2_struct_0('#skF_4'))=a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_51, c_138])).
% 3.44/1.53  tff(c_40, plain, (k2_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.44/1.53  tff(c_144, plain, (a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_143, c_40])).
% 3.44/1.53  tff(c_8, plain, (![A_5]: (r2_hidden('#skF_1'(A_5), A_5) | k1_xboole_0=A_5)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.44/1.53  tff(c_164, plain, (![A_82, B_83, C_84]: ('#skF_2'(A_82, B_83, C_84)=A_82 | ~r2_hidden(A_82, a_2_1_orders_2(B_83, C_84)) | ~m1_subset_1(C_84, k1_zfmisc_1(u1_struct_0(B_83))) | ~l1_orders_2(B_83) | ~v5_orders_2(B_83) | ~v4_orders_2(B_83) | ~v3_orders_2(B_83) | v2_struct_0(B_83))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.44/1.53  tff(c_210, plain, (![B_97, C_98]: ('#skF_2'('#skF_1'(a_2_1_orders_2(B_97, C_98)), B_97, C_98)='#skF_1'(a_2_1_orders_2(B_97, C_98)) | ~m1_subset_1(C_98, k1_zfmisc_1(u1_struct_0(B_97))) | ~l1_orders_2(B_97) | ~v5_orders_2(B_97) | ~v4_orders_2(B_97) | ~v3_orders_2(B_97) | v2_struct_0(B_97) | a_2_1_orders_2(B_97, C_98)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_164])).
% 3.44/1.53  tff(c_212, plain, (![C_98]: ('#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4', C_98)), '#skF_4', C_98)='#skF_1'(a_2_1_orders_2('#skF_4', C_98)) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | a_2_1_orders_2('#skF_4', C_98)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_73, c_210])).
% 3.44/1.53  tff(c_217, plain, (![C_98]: ('#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4', C_98)), '#skF_4', C_98)='#skF_1'(a_2_1_orders_2('#skF_4', C_98)) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | a_2_1_orders_2('#skF_4', C_98)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_212])).
% 3.44/1.53  tff(c_220, plain, (![C_99]: ('#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4', C_99)), '#skF_4', C_99)='#skF_1'(a_2_1_orders_2('#skF_4', C_99)) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_struct_0('#skF_4'))) | a_2_1_orders_2('#skF_4', C_99)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_50, c_217])).
% 3.44/1.53  tff(c_223, plain, ('#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), '#skF_4', k2_struct_0('#skF_4'))='#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_51, c_220])).
% 3.44/1.53  tff(c_226, plain, ('#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), '#skF_4', k2_struct_0('#skF_4'))='#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_144, c_223])).
% 3.44/1.53  tff(c_173, plain, (![A_85, B_86, C_87]: (m1_subset_1('#skF_2'(A_85, B_86, C_87), u1_struct_0(B_86)) | ~r2_hidden(A_85, a_2_1_orders_2(B_86, C_87)) | ~m1_subset_1(C_87, k1_zfmisc_1(u1_struct_0(B_86))) | ~l1_orders_2(B_86) | ~v5_orders_2(B_86) | ~v4_orders_2(B_86) | ~v3_orders_2(B_86) | v2_struct_0(B_86))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.44/1.53  tff(c_178, plain, (![A_85, C_87]: (m1_subset_1('#skF_2'(A_85, '#skF_4', C_87), k2_struct_0('#skF_4')) | ~r2_hidden(A_85, a_2_1_orders_2('#skF_4', C_87)) | ~m1_subset_1(C_87, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_73, c_173])).
% 3.44/1.53  tff(c_181, plain, (![A_85, C_87]: (m1_subset_1('#skF_2'(A_85, '#skF_4', C_87), k2_struct_0('#skF_4')) | ~r2_hidden(A_85, a_2_1_orders_2('#skF_4', C_87)) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_73, c_178])).
% 3.44/1.53  tff(c_182, plain, (![A_85, C_87]: (m1_subset_1('#skF_2'(A_85, '#skF_4', C_87), k2_struct_0('#skF_4')) | ~r2_hidden(A_85, a_2_1_orders_2('#skF_4', C_87)) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_181])).
% 3.44/1.53  tff(c_240, plain, (m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_226, c_182])).
% 3.44/1.53  tff(c_247, plain, (m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_240])).
% 3.44/1.53  tff(c_252, plain, (~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_247])).
% 3.44/1.53  tff(c_258, plain, (a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_252])).
% 3.44/1.53  tff(c_264, plain, $false, inference(negUnitSimplification, [status(thm)], [c_144, c_258])).
% 3.44/1.53  tff(c_265, plain, (m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_247])).
% 3.44/1.53  tff(c_6, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.44/1.53  tff(c_266, plain, (r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_247])).
% 3.44/1.53  tff(c_800, plain, (![B_163, A_164, C_165, E_166]: (r2_orders_2(B_163, '#skF_2'(A_164, B_163, C_165), E_166) | ~r2_hidden(E_166, C_165) | ~m1_subset_1(E_166, u1_struct_0(B_163)) | ~r2_hidden(A_164, a_2_1_orders_2(B_163, C_165)) | ~m1_subset_1(C_165, k1_zfmisc_1(u1_struct_0(B_163))) | ~l1_orders_2(B_163) | ~v5_orders_2(B_163) | ~v4_orders_2(B_163) | ~v3_orders_2(B_163) | v2_struct_0(B_163))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.44/1.53  tff(c_802, plain, (![A_164, C_165, E_166]: (r2_orders_2('#skF_4', '#skF_2'(A_164, '#skF_4', C_165), E_166) | ~r2_hidden(E_166, C_165) | ~m1_subset_1(E_166, u1_struct_0('#skF_4')) | ~r2_hidden(A_164, a_2_1_orders_2('#skF_4', C_165)) | ~m1_subset_1(C_165, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_73, c_800])).
% 3.44/1.53  tff(c_807, plain, (![A_164, C_165, E_166]: (r2_orders_2('#skF_4', '#skF_2'(A_164, '#skF_4', C_165), E_166) | ~r2_hidden(E_166, C_165) | ~m1_subset_1(E_166, k2_struct_0('#skF_4')) | ~r2_hidden(A_164, a_2_1_orders_2('#skF_4', C_165)) | ~m1_subset_1(C_165, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_73, c_802])).
% 3.44/1.53  tff(c_810, plain, (![A_167, C_168, E_169]: (r2_orders_2('#skF_4', '#skF_2'(A_167, '#skF_4', C_168), E_169) | ~r2_hidden(E_169, C_168) | ~m1_subset_1(E_169, k2_struct_0('#skF_4')) | ~r2_hidden(A_167, a_2_1_orders_2('#skF_4', C_168)) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_807])).
% 3.44/1.53  tff(c_815, plain, (![A_170, E_171]: (r2_orders_2('#skF_4', '#skF_2'(A_170, '#skF_4', k2_struct_0('#skF_4')), E_171) | ~r2_hidden(E_171, k2_struct_0('#skF_4')) | ~m1_subset_1(E_171, k2_struct_0('#skF_4')) | ~r2_hidden(A_170, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_51, c_810])).
% 3.44/1.53  tff(c_826, plain, (![E_171]: (r2_orders_2('#skF_4', '#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), E_171) | ~r2_hidden(E_171, k2_struct_0('#skF_4')) | ~m1_subset_1(E_171, k2_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_226, c_815])).
% 3.44/1.53  tff(c_839, plain, (![E_172]: (r2_orders_2('#skF_4', '#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), E_172) | ~r2_hidden(E_172, k2_struct_0('#skF_4')) | ~m1_subset_1(E_172, k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_266, c_826])).
% 3.44/1.53  tff(c_20, plain, (![A_17, C_23]: (~r2_orders_2(A_17, C_23, C_23) | ~m1_subset_1(C_23, u1_struct_0(A_17)) | ~l1_orders_2(A_17))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.44/1.53  tff(c_847, plain, (~m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_839, c_20])).
% 3.44/1.53  tff(c_857, plain, (~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_265, c_42, c_265, c_73, c_847])).
% 3.44/1.53  tff(c_881, plain, (v1_xboole_0(k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_6, c_857])).
% 3.44/1.53  tff(c_884, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_265, c_881])).
% 3.44/1.53  tff(c_886, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_884])).
% 3.44/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.53  
% 3.44/1.53  Inference rules
% 3.44/1.53  ----------------------
% 3.44/1.53  #Ref     : 0
% 3.44/1.53  #Sup     : 157
% 3.44/1.53  #Fact    : 0
% 3.44/1.53  #Define  : 0
% 3.44/1.53  #Split   : 5
% 3.44/1.53  #Chain   : 0
% 3.44/1.53  #Close   : 0
% 3.44/1.53  
% 3.44/1.53  Ordering : KBO
% 3.44/1.53  
% 3.44/1.53  Simplification rules
% 3.44/1.53  ----------------------
% 3.44/1.53  #Subsume      : 14
% 3.44/1.53  #Demod        : 380
% 3.44/1.53  #Tautology    : 56
% 3.44/1.53  #SimpNegUnit  : 58
% 3.44/1.53  #BackRed      : 18
% 3.44/1.53  
% 3.44/1.53  #Partial instantiations: 0
% 3.44/1.53  #Strategies tried      : 1
% 3.44/1.53  
% 3.44/1.53  Timing (in seconds)
% 3.44/1.53  ----------------------
% 3.44/1.53  Preprocessing        : 0.33
% 3.44/1.53  Parsing              : 0.17
% 3.44/1.53  CNF conversion       : 0.02
% 3.44/1.53  Main loop            : 0.43
% 3.44/1.53  Inferencing          : 0.16
% 3.44/1.53  Reduction            : 0.14
% 3.44/1.53  Demodulation         : 0.10
% 3.44/1.53  BG Simplification    : 0.02
% 3.44/1.53  Subsumption          : 0.07
% 3.44/1.53  Abstraction          : 0.03
% 3.44/1.53  MUC search           : 0.00
% 3.44/1.53  Cooper               : 0.00
% 3.44/1.53  Total                : 0.79
% 3.44/1.53  Index Insertion      : 0.00
% 3.44/1.53  Index Deletion       : 0.00
% 3.44/1.53  Index Matching       : 0.00
% 3.44/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
