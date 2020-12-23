%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:28 EST 2020

% Result     : Theorem 7.46s
% Output     : CNFRefutation 7.46s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 721 expanded)
%              Number of leaves         :   40 ( 285 expanded)
%              Depth                    :   22
%              Number of atoms          :  283 (2127 expanded)
%              Number of equality atoms :   31 ( 376 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k3_mcart_1 > k2_zfmisc_1 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(a_2_1_orders_2,type,(
    a_2_1_orders_2: ( $i * $i ) > $i )).

tff(k2_orders_2,type,(
    k2_orders_2: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_189,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => k2_orders_2(A,k2_struct_0(A)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_orders_2)).

tff(f_148,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_98,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_129,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_orders_2(A,B) = a_2_1_orders_2(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_orders_2)).

tff(f_90,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_175,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

tff(f_58,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_144,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_orders_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_orders_2)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( ! [C] :
            ( m1_subset_1(C,A)
           => r2_hidden(C,B) )
       => A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_113,axiom,(
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

tff(c_66,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_50,plain,(
    ! [A_46] :
      ( l1_struct_0(A_46)
      | ~ l1_orders_2(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_119,plain,(
    ! [A_70] :
      ( u1_struct_0(A_70) = k2_struct_0(A_70)
      | ~ l1_struct_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_125,plain,(
    ! [A_72] :
      ( u1_struct_0(A_72) = k2_struct_0(A_72)
      | ~ l1_orders_2(A_72) ) ),
    inference(resolution,[status(thm)],[c_50,c_119])).

tff(c_129,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_125])).

tff(c_191,plain,(
    ! [A_84] :
      ( m1_subset_1(k2_struct_0(A_84),k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_struct_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_197,plain,
    ( m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5')))
    | ~ l1_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_191])).

tff(c_199,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_197])).

tff(c_202,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_199])).

tff(c_206,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_202])).

tff(c_207,plain,(
    m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_197])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_72,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_70,plain,(
    v4_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_68,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_481,plain,(
    ! [A_146,B_147] :
      ( k2_orders_2(A_146,B_147) = a_2_1_orders_2(A_146,B_147)
      | ~ m1_subset_1(B_147,k1_zfmisc_1(u1_struct_0(A_146)))
      | ~ l1_orders_2(A_146)
      | ~ v5_orders_2(A_146)
      | ~ v4_orders_2(A_146)
      | ~ v3_orders_2(A_146)
      | v2_struct_0(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_495,plain,(
    ! [B_147] :
      ( k2_orders_2('#skF_5',B_147) = a_2_1_orders_2('#skF_5',B_147)
      | ~ m1_subset_1(B_147,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_481])).

tff(c_508,plain,(
    ! [B_147] :
      ( k2_orders_2('#skF_5',B_147) = a_2_1_orders_2('#skF_5',B_147)
      | ~ m1_subset_1(B_147,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_66,c_495])).

tff(c_512,plain,(
    ! [B_148] :
      ( k2_orders_2('#skF_5',B_148) = a_2_1_orders_2('#skF_5',B_148)
      | ~ m1_subset_1(B_148,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_508])).

tff(c_533,plain,(
    k2_orders_2('#skF_5',k2_struct_0('#skF_5')) = a_2_1_orders_2('#skF_5',k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_207,c_512])).

tff(c_64,plain,(
    k2_orders_2('#skF_5',k2_struct_0('#skF_5')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_541,plain,(
    a_2_1_orders_2('#skF_5',k2_struct_0('#skF_5')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_533,c_64])).

tff(c_30,plain,(
    ! [A_18] :
      ( r2_hidden('#skF_2'(A_18),A_18)
      | k1_xboole_0 = A_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1223,plain,(
    ! [A_182,B_183,C_184] :
      ( m1_subset_1('#skF_3'(A_182,B_183,C_184),u1_struct_0(B_183))
      | ~ r2_hidden(A_182,a_2_1_orders_2(B_183,C_184))
      | ~ m1_subset_1(C_184,k1_zfmisc_1(u1_struct_0(B_183)))
      | ~ l1_orders_2(B_183)
      | ~ v5_orders_2(B_183)
      | ~ v4_orders_2(B_183)
      | ~ v3_orders_2(B_183)
      | v2_struct_0(B_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_1231,plain,(
    ! [A_182,C_184] :
      ( m1_subset_1('#skF_3'(A_182,'#skF_5',C_184),k2_struct_0('#skF_5'))
      | ~ r2_hidden(A_182,a_2_1_orders_2('#skF_5',C_184))
      | ~ m1_subset_1(C_184,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_1223])).

tff(c_1235,plain,(
    ! [A_182,C_184] :
      ( m1_subset_1('#skF_3'(A_182,'#skF_5',C_184),k2_struct_0('#skF_5'))
      | ~ r2_hidden(A_182,a_2_1_orders_2('#skF_5',C_184))
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_66,c_129,c_1231])).

tff(c_1236,plain,(
    ! [A_182,C_184] :
      ( m1_subset_1('#skF_3'(A_182,'#skF_5',C_184),k2_struct_0('#skF_5'))
      | ~ r2_hidden(A_182,a_2_1_orders_2('#skF_5',C_184))
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1235])).

tff(c_22,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_536,plain,(
    k2_orders_2('#skF_5',k1_xboole_0) = a_2_1_orders_2('#skF_5',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_22,c_512])).

tff(c_684,plain,(
    ! [A_155,B_156] :
      ( m1_subset_1(k2_orders_2(A_155,B_156),k1_zfmisc_1(u1_struct_0(A_155)))
      | ~ m1_subset_1(B_156,k1_zfmisc_1(u1_struct_0(A_155)))
      | ~ l1_orders_2(A_155)
      | ~ v5_orders_2(A_155)
      | ~ v4_orders_2(A_155)
      | ~ v3_orders_2(A_155)
      | v2_struct_0(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_701,plain,
    ( m1_subset_1(a_2_1_orders_2('#skF_5',k1_xboole_0),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_536,c_684])).

tff(c_713,plain,
    ( m1_subset_1(a_2_1_orders_2('#skF_5',k1_xboole_0),k1_zfmisc_1(k2_struct_0('#skF_5')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_66,c_22,c_129,c_129,c_701])).

tff(c_714,plain,(
    m1_subset_1(a_2_1_orders_2('#skF_5',k1_xboole_0),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_713])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1('#skF_1'(A_7,B_8),A_7)
      | B_8 = A_7
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_99,plain,(
    ! [A_64,B_65] : ~ r2_hidden(A_64,k2_zfmisc_1(A_64,B_65)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_102,plain,(
    ! [A_1] : ~ r2_hidden(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_99])).

tff(c_2746,plain,(
    ! [D_266,B_267,C_268] :
      ( r2_hidden('#skF_4'(D_266,B_267,C_268,D_266),C_268)
      | r2_hidden(D_266,a_2_1_orders_2(B_267,C_268))
      | ~ m1_subset_1(D_266,u1_struct_0(B_267))
      | ~ m1_subset_1(C_268,k1_zfmisc_1(u1_struct_0(B_267)))
      | ~ l1_orders_2(B_267)
      | ~ v5_orders_2(B_267)
      | ~ v4_orders_2(B_267)
      | ~ v3_orders_2(B_267)
      | v2_struct_0(B_267) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_2761,plain,(
    ! [D_266,C_268] :
      ( r2_hidden('#skF_4'(D_266,'#skF_5',C_268,D_266),C_268)
      | r2_hidden(D_266,a_2_1_orders_2('#skF_5',C_268))
      | ~ m1_subset_1(D_266,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_268,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_2746])).

tff(c_2774,plain,(
    ! [D_266,C_268] :
      ( r2_hidden('#skF_4'(D_266,'#skF_5',C_268,D_266),C_268)
      | r2_hidden(D_266,a_2_1_orders_2('#skF_5',C_268))
      | ~ m1_subset_1(D_266,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_268,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_66,c_129,c_2761])).

tff(c_2828,plain,(
    ! [D_272,C_273] :
      ( r2_hidden('#skF_4'(D_272,'#skF_5',C_273,D_272),C_273)
      | r2_hidden(D_272,a_2_1_orders_2('#skF_5',C_273))
      | ~ m1_subset_1(D_272,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_273,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_2774])).

tff(c_2855,plain,(
    ! [D_272] :
      ( r2_hidden('#skF_4'(D_272,'#skF_5',k1_xboole_0,D_272),k1_xboole_0)
      | r2_hidden(D_272,a_2_1_orders_2('#skF_5',k1_xboole_0))
      | ~ m1_subset_1(D_272,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_22,c_2828])).

tff(c_2869,plain,(
    ! [D_274] :
      ( r2_hidden(D_274,a_2_1_orders_2('#skF_5',k1_xboole_0))
      | ~ m1_subset_1(D_274,k2_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_2855])).

tff(c_18,plain,(
    ! [A_7,B_8] :
      ( ~ r2_hidden('#skF_1'(A_7,B_8),B_8)
      | B_8 = A_7
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4682,plain,(
    ! [A_361] :
      ( a_2_1_orders_2('#skF_5',k1_xboole_0) = A_361
      | ~ m1_subset_1(a_2_1_orders_2('#skF_5',k1_xboole_0),k1_zfmisc_1(A_361))
      | ~ m1_subset_1('#skF_1'(A_361,a_2_1_orders_2('#skF_5',k1_xboole_0)),k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_2869,c_18])).

tff(c_4686,plain,
    ( a_2_1_orders_2('#skF_5',k1_xboole_0) = k2_struct_0('#skF_5')
    | ~ m1_subset_1(a_2_1_orders_2('#skF_5',k1_xboole_0),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_20,c_4682])).

tff(c_4692,plain,(
    a_2_1_orders_2('#skF_5',k1_xboole_0) = k2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_714,c_4686])).

tff(c_2767,plain,(
    ! [D_266,B_267] :
      ( r2_hidden('#skF_4'(D_266,B_267,k1_xboole_0,D_266),k1_xboole_0)
      | r2_hidden(D_266,a_2_1_orders_2(B_267,k1_xboole_0))
      | ~ m1_subset_1(D_266,u1_struct_0(B_267))
      | ~ l1_orders_2(B_267)
      | ~ v5_orders_2(B_267)
      | ~ v4_orders_2(B_267)
      | ~ v3_orders_2(B_267)
      | v2_struct_0(B_267) ) ),
    inference(resolution,[status(thm)],[c_22,c_2746])).

tff(c_2779,plain,(
    ! [D_266,B_267] :
      ( r2_hidden(D_266,a_2_1_orders_2(B_267,k1_xboole_0))
      | ~ m1_subset_1(D_266,u1_struct_0(B_267))
      | ~ l1_orders_2(B_267)
      | ~ v5_orders_2(B_267)
      | ~ v4_orders_2(B_267)
      | ~ v3_orders_2(B_267)
      | v2_struct_0(B_267) ) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_2767])).

tff(c_4730,plain,(
    ! [D_266] :
      ( r2_hidden(D_266,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(D_266,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4692,c_2779])).

tff(c_4736,plain,(
    ! [D_266] :
      ( r2_hidden(D_266,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(D_266,k2_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_66,c_129,c_4730])).

tff(c_4737,plain,(
    ! [D_266] :
      ( r2_hidden(D_266,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(D_266,k2_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_4736])).

tff(c_4716,plain,(
    k2_orders_2('#skF_5',k1_xboole_0) = k2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4692,c_536])).

tff(c_48,plain,(
    ! [A_44,B_45] :
      ( m1_subset_1(k2_orders_2(A_44,B_45),k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_orders_2(A_44)
      | ~ v5_orders_2(A_44)
      | ~ v4_orders_2(A_44)
      | ~ v3_orders_2(A_44)
      | v2_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_3261,plain,(
    ! [B_297,A_298,C_299,E_300] :
      ( r2_orders_2(B_297,'#skF_3'(A_298,B_297,C_299),E_300)
      | ~ r2_hidden(E_300,C_299)
      | ~ m1_subset_1(E_300,u1_struct_0(B_297))
      | ~ r2_hidden(A_298,a_2_1_orders_2(B_297,C_299))
      | ~ m1_subset_1(C_299,k1_zfmisc_1(u1_struct_0(B_297)))
      | ~ l1_orders_2(B_297)
      | ~ v5_orders_2(B_297)
      | ~ v4_orders_2(B_297)
      | ~ v3_orders_2(B_297)
      | v2_struct_0(B_297) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_6833,plain,(
    ! [A_460,A_461,B_462,E_463] :
      ( r2_orders_2(A_460,'#skF_3'(A_461,A_460,k2_orders_2(A_460,B_462)),E_463)
      | ~ r2_hidden(E_463,k2_orders_2(A_460,B_462))
      | ~ m1_subset_1(E_463,u1_struct_0(A_460))
      | ~ r2_hidden(A_461,a_2_1_orders_2(A_460,k2_orders_2(A_460,B_462)))
      | ~ m1_subset_1(B_462,k1_zfmisc_1(u1_struct_0(A_460)))
      | ~ l1_orders_2(A_460)
      | ~ v5_orders_2(A_460)
      | ~ v4_orders_2(A_460)
      | ~ v3_orders_2(A_460)
      | v2_struct_0(A_460) ) ),
    inference(resolution,[status(thm)],[c_48,c_3261])).

tff(c_6847,plain,(
    ! [A_461,E_463] :
      ( r2_orders_2('#skF_5','#skF_3'(A_461,'#skF_5',k2_struct_0('#skF_5')),E_463)
      | ~ r2_hidden(E_463,k2_orders_2('#skF_5',k1_xboole_0))
      | ~ m1_subset_1(E_463,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_461,a_2_1_orders_2('#skF_5',k2_orders_2('#skF_5',k1_xboole_0)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4716,c_6833])).

tff(c_6861,plain,(
    ! [A_461,E_463] :
      ( r2_orders_2('#skF_5','#skF_3'(A_461,'#skF_5',k2_struct_0('#skF_5')),E_463)
      | ~ r2_hidden(E_463,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(E_463,k2_struct_0('#skF_5'))
      | ~ r2_hidden(A_461,a_2_1_orders_2('#skF_5',k2_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_66,c_22,c_129,c_4716,c_129,c_4716,c_6847])).

tff(c_6892,plain,(
    ! [A_465,E_466] :
      ( r2_orders_2('#skF_5','#skF_3'(A_465,'#skF_5',k2_struct_0('#skF_5')),E_466)
      | ~ r2_hidden(E_466,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(E_466,k2_struct_0('#skF_5'))
      | ~ r2_hidden(A_465,a_2_1_orders_2('#skF_5',k2_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_6861])).

tff(c_42,plain,(
    ! [A_34,C_40] :
      ( ~ r2_orders_2(A_34,C_40,C_40)
      | ~ m1_subset_1(C_40,u1_struct_0(A_34))
      | ~ l1_orders_2(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_6900,plain,(
    ! [A_465] :
      ( ~ m1_subset_1('#skF_3'(A_465,'#skF_5',k2_struct_0('#skF_5')),u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ r2_hidden('#skF_3'(A_465,'#skF_5',k2_struct_0('#skF_5')),k2_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_3'(A_465,'#skF_5',k2_struct_0('#skF_5')),k2_struct_0('#skF_5'))
      | ~ r2_hidden(A_465,a_2_1_orders_2('#skF_5',k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_6892,c_42])).

tff(c_7076,plain,(
    ! [A_481] :
      ( ~ r2_hidden('#skF_3'(A_481,'#skF_5',k2_struct_0('#skF_5')),k2_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_3'(A_481,'#skF_5',k2_struct_0('#skF_5')),k2_struct_0('#skF_5'))
      | ~ r2_hidden(A_481,a_2_1_orders_2('#skF_5',k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_129,c_6900])).

tff(c_7095,plain,(
    ! [A_482] :
      ( ~ r2_hidden(A_482,a_2_1_orders_2('#skF_5',k2_struct_0('#skF_5')))
      | ~ m1_subset_1('#skF_3'(A_482,'#skF_5',k2_struct_0('#skF_5')),k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_4737,c_7076])).

tff(c_7105,plain,(
    ! [A_182] :
      ( ~ r2_hidden(A_182,a_2_1_orders_2('#skF_5',k2_struct_0('#skF_5')))
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_1236,c_7095])).

tff(c_7122,plain,(
    ! [A_483] : ~ r2_hidden(A_483,a_2_1_orders_2('#skF_5',k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_7105])).

tff(c_7130,plain,(
    a_2_1_orders_2('#skF_5',k2_struct_0('#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_7122])).

tff(c_7136,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_541,c_7130])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:50:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.46/2.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.46/2.60  
% 7.46/2.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.46/2.60  %$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k3_mcart_1 > k2_zfmisc_1 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_4 > #skF_3 > #skF_1
% 7.46/2.60  
% 7.46/2.60  %Foreground sorts:
% 7.46/2.60  
% 7.46/2.60  
% 7.46/2.60  %Background operators:
% 7.46/2.60  
% 7.46/2.60  
% 7.46/2.60  %Foreground operators:
% 7.46/2.60  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.46/2.60  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 7.46/2.60  tff('#skF_2', type, '#skF_2': $i > $i).
% 7.46/2.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.46/2.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.46/2.60  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 7.46/2.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.46/2.60  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 7.46/2.60  tff(a_2_1_orders_2, type, a_2_1_orders_2: ($i * $i) > $i).
% 7.46/2.60  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 7.46/2.60  tff('#skF_5', type, '#skF_5': $i).
% 7.46/2.60  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 7.46/2.60  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 7.46/2.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.46/2.60  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 7.46/2.60  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 7.46/2.60  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 7.46/2.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.46/2.60  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.46/2.60  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.46/2.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.46/2.60  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 7.46/2.60  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.46/2.60  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.46/2.60  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 7.46/2.60  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.46/2.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.46/2.60  
% 7.46/2.62  tff(f_189, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k2_orders_2(A, k2_struct_0(A)) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_orders_2)).
% 7.46/2.62  tff(f_148, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 7.46/2.62  tff(f_94, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 7.46/2.62  tff(f_98, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 7.46/2.62  tff(f_129, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_orders_2(A, B) = a_2_1_orders_2(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_orders_2)).
% 7.46/2.62  tff(f_90, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 7.46/2.62  tff(f_175, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_1_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, D, E))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_1_orders_2)).
% 7.46/2.62  tff(f_58, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 7.46/2.62  tff(f_144, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_orders_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_orders_2)).
% 7.46/2.62  tff(f_56, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ((![C]: (m1_subset_1(C, A) => r2_hidden(C, B))) => (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_subset_1)).
% 7.46/2.62  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.46/2.62  tff(f_34, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 7.46/2.62  tff(f_113, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_orders_2)).
% 7.46/2.62  tff(c_66, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_189])).
% 7.46/2.62  tff(c_50, plain, (![A_46]: (l1_struct_0(A_46) | ~l1_orders_2(A_46))), inference(cnfTransformation, [status(thm)], [f_148])).
% 7.46/2.62  tff(c_119, plain, (![A_70]: (u1_struct_0(A_70)=k2_struct_0(A_70) | ~l1_struct_0(A_70))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.46/2.62  tff(c_125, plain, (![A_72]: (u1_struct_0(A_72)=k2_struct_0(A_72) | ~l1_orders_2(A_72))), inference(resolution, [status(thm)], [c_50, c_119])).
% 7.46/2.62  tff(c_129, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_66, c_125])).
% 7.46/2.62  tff(c_191, plain, (![A_84]: (m1_subset_1(k2_struct_0(A_84), k1_zfmisc_1(u1_struct_0(A_84))) | ~l1_struct_0(A_84))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.46/2.62  tff(c_197, plain, (m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_129, c_191])).
% 7.46/2.62  tff(c_199, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_197])).
% 7.46/2.62  tff(c_202, plain, (~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_50, c_199])).
% 7.46/2.62  tff(c_206, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_202])).
% 7.46/2.62  tff(c_207, plain, (m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_197])).
% 7.46/2.62  tff(c_74, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_189])).
% 7.46/2.62  tff(c_72, plain, (v3_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_189])).
% 7.46/2.62  tff(c_70, plain, (v4_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_189])).
% 7.46/2.62  tff(c_68, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_189])).
% 7.46/2.62  tff(c_481, plain, (![A_146, B_147]: (k2_orders_2(A_146, B_147)=a_2_1_orders_2(A_146, B_147) | ~m1_subset_1(B_147, k1_zfmisc_1(u1_struct_0(A_146))) | ~l1_orders_2(A_146) | ~v5_orders_2(A_146) | ~v4_orders_2(A_146) | ~v3_orders_2(A_146) | v2_struct_0(A_146))), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.46/2.62  tff(c_495, plain, (![B_147]: (k2_orders_2('#skF_5', B_147)=a_2_1_orders_2('#skF_5', B_147) | ~m1_subset_1(B_147, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_129, c_481])).
% 7.46/2.62  tff(c_508, plain, (![B_147]: (k2_orders_2('#skF_5', B_147)=a_2_1_orders_2('#skF_5', B_147) | ~m1_subset_1(B_147, k1_zfmisc_1(k2_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_66, c_495])).
% 7.46/2.62  tff(c_512, plain, (![B_148]: (k2_orders_2('#skF_5', B_148)=a_2_1_orders_2('#skF_5', B_148) | ~m1_subset_1(B_148, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_74, c_508])).
% 7.46/2.62  tff(c_533, plain, (k2_orders_2('#skF_5', k2_struct_0('#skF_5'))=a_2_1_orders_2('#skF_5', k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_207, c_512])).
% 7.46/2.62  tff(c_64, plain, (k2_orders_2('#skF_5', k2_struct_0('#skF_5'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_189])).
% 7.46/2.62  tff(c_541, plain, (a_2_1_orders_2('#skF_5', k2_struct_0('#skF_5'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_533, c_64])).
% 7.46/2.62  tff(c_30, plain, (![A_18]: (r2_hidden('#skF_2'(A_18), A_18) | k1_xboole_0=A_18)), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.46/2.62  tff(c_1223, plain, (![A_182, B_183, C_184]: (m1_subset_1('#skF_3'(A_182, B_183, C_184), u1_struct_0(B_183)) | ~r2_hidden(A_182, a_2_1_orders_2(B_183, C_184)) | ~m1_subset_1(C_184, k1_zfmisc_1(u1_struct_0(B_183))) | ~l1_orders_2(B_183) | ~v5_orders_2(B_183) | ~v4_orders_2(B_183) | ~v3_orders_2(B_183) | v2_struct_0(B_183))), inference(cnfTransformation, [status(thm)], [f_175])).
% 7.46/2.62  tff(c_1231, plain, (![A_182, C_184]: (m1_subset_1('#skF_3'(A_182, '#skF_5', C_184), k2_struct_0('#skF_5')) | ~r2_hidden(A_182, a_2_1_orders_2('#skF_5', C_184)) | ~m1_subset_1(C_184, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_129, c_1223])).
% 7.46/2.62  tff(c_1235, plain, (![A_182, C_184]: (m1_subset_1('#skF_3'(A_182, '#skF_5', C_184), k2_struct_0('#skF_5')) | ~r2_hidden(A_182, a_2_1_orders_2('#skF_5', C_184)) | ~m1_subset_1(C_184, k1_zfmisc_1(k2_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_66, c_129, c_1231])).
% 7.46/2.62  tff(c_1236, plain, (![A_182, C_184]: (m1_subset_1('#skF_3'(A_182, '#skF_5', C_184), k2_struct_0('#skF_5')) | ~r2_hidden(A_182, a_2_1_orders_2('#skF_5', C_184)) | ~m1_subset_1(C_184, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_74, c_1235])).
% 7.46/2.62  tff(c_22, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.46/2.62  tff(c_536, plain, (k2_orders_2('#skF_5', k1_xboole_0)=a_2_1_orders_2('#skF_5', k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_512])).
% 7.46/2.62  tff(c_684, plain, (![A_155, B_156]: (m1_subset_1(k2_orders_2(A_155, B_156), k1_zfmisc_1(u1_struct_0(A_155))) | ~m1_subset_1(B_156, k1_zfmisc_1(u1_struct_0(A_155))) | ~l1_orders_2(A_155) | ~v5_orders_2(A_155) | ~v4_orders_2(A_155) | ~v3_orders_2(A_155) | v2_struct_0(A_155))), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.46/2.62  tff(c_701, plain, (m1_subset_1(a_2_1_orders_2('#skF_5', k1_xboole_0), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_536, c_684])).
% 7.46/2.62  tff(c_713, plain, (m1_subset_1(a_2_1_orders_2('#skF_5', k1_xboole_0), k1_zfmisc_1(k2_struct_0('#skF_5'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_66, c_22, c_129, c_129, c_701])).
% 7.46/2.62  tff(c_714, plain, (m1_subset_1(a_2_1_orders_2('#skF_5', k1_xboole_0), k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_74, c_713])).
% 7.46/2.62  tff(c_20, plain, (![A_7, B_8]: (m1_subset_1('#skF_1'(A_7, B_8), A_7) | B_8=A_7 | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.46/2.62  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.46/2.62  tff(c_99, plain, (![A_64, B_65]: (~r2_hidden(A_64, k2_zfmisc_1(A_64, B_65)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.46/2.62  tff(c_102, plain, (![A_1]: (~r2_hidden(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_99])).
% 7.46/2.62  tff(c_2746, plain, (![D_266, B_267, C_268]: (r2_hidden('#skF_4'(D_266, B_267, C_268, D_266), C_268) | r2_hidden(D_266, a_2_1_orders_2(B_267, C_268)) | ~m1_subset_1(D_266, u1_struct_0(B_267)) | ~m1_subset_1(C_268, k1_zfmisc_1(u1_struct_0(B_267))) | ~l1_orders_2(B_267) | ~v5_orders_2(B_267) | ~v4_orders_2(B_267) | ~v3_orders_2(B_267) | v2_struct_0(B_267))), inference(cnfTransformation, [status(thm)], [f_175])).
% 7.46/2.62  tff(c_2761, plain, (![D_266, C_268]: (r2_hidden('#skF_4'(D_266, '#skF_5', C_268, D_266), C_268) | r2_hidden(D_266, a_2_1_orders_2('#skF_5', C_268)) | ~m1_subset_1(D_266, u1_struct_0('#skF_5')) | ~m1_subset_1(C_268, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_129, c_2746])).
% 7.46/2.62  tff(c_2774, plain, (![D_266, C_268]: (r2_hidden('#skF_4'(D_266, '#skF_5', C_268, D_266), C_268) | r2_hidden(D_266, a_2_1_orders_2('#skF_5', C_268)) | ~m1_subset_1(D_266, k2_struct_0('#skF_5')) | ~m1_subset_1(C_268, k1_zfmisc_1(k2_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_66, c_129, c_2761])).
% 7.46/2.62  tff(c_2828, plain, (![D_272, C_273]: (r2_hidden('#skF_4'(D_272, '#skF_5', C_273, D_272), C_273) | r2_hidden(D_272, a_2_1_orders_2('#skF_5', C_273)) | ~m1_subset_1(D_272, k2_struct_0('#skF_5')) | ~m1_subset_1(C_273, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_74, c_2774])).
% 7.46/2.62  tff(c_2855, plain, (![D_272]: (r2_hidden('#skF_4'(D_272, '#skF_5', k1_xboole_0, D_272), k1_xboole_0) | r2_hidden(D_272, a_2_1_orders_2('#skF_5', k1_xboole_0)) | ~m1_subset_1(D_272, k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_22, c_2828])).
% 7.46/2.62  tff(c_2869, plain, (![D_274]: (r2_hidden(D_274, a_2_1_orders_2('#skF_5', k1_xboole_0)) | ~m1_subset_1(D_274, k2_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_102, c_2855])).
% 7.46/2.62  tff(c_18, plain, (![A_7, B_8]: (~r2_hidden('#skF_1'(A_7, B_8), B_8) | B_8=A_7 | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.46/2.62  tff(c_4682, plain, (![A_361]: (a_2_1_orders_2('#skF_5', k1_xboole_0)=A_361 | ~m1_subset_1(a_2_1_orders_2('#skF_5', k1_xboole_0), k1_zfmisc_1(A_361)) | ~m1_subset_1('#skF_1'(A_361, a_2_1_orders_2('#skF_5', k1_xboole_0)), k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_2869, c_18])).
% 7.46/2.62  tff(c_4686, plain, (a_2_1_orders_2('#skF_5', k1_xboole_0)=k2_struct_0('#skF_5') | ~m1_subset_1(a_2_1_orders_2('#skF_5', k1_xboole_0), k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_20, c_4682])).
% 7.46/2.62  tff(c_4692, plain, (a_2_1_orders_2('#skF_5', k1_xboole_0)=k2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_714, c_4686])).
% 7.46/2.62  tff(c_2767, plain, (![D_266, B_267]: (r2_hidden('#skF_4'(D_266, B_267, k1_xboole_0, D_266), k1_xboole_0) | r2_hidden(D_266, a_2_1_orders_2(B_267, k1_xboole_0)) | ~m1_subset_1(D_266, u1_struct_0(B_267)) | ~l1_orders_2(B_267) | ~v5_orders_2(B_267) | ~v4_orders_2(B_267) | ~v3_orders_2(B_267) | v2_struct_0(B_267))), inference(resolution, [status(thm)], [c_22, c_2746])).
% 7.46/2.62  tff(c_2779, plain, (![D_266, B_267]: (r2_hidden(D_266, a_2_1_orders_2(B_267, k1_xboole_0)) | ~m1_subset_1(D_266, u1_struct_0(B_267)) | ~l1_orders_2(B_267) | ~v5_orders_2(B_267) | ~v4_orders_2(B_267) | ~v3_orders_2(B_267) | v2_struct_0(B_267))), inference(negUnitSimplification, [status(thm)], [c_102, c_2767])).
% 7.46/2.62  tff(c_4730, plain, (![D_266]: (r2_hidden(D_266, k2_struct_0('#skF_5')) | ~m1_subset_1(D_266, u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_4692, c_2779])).
% 7.46/2.62  tff(c_4736, plain, (![D_266]: (r2_hidden(D_266, k2_struct_0('#skF_5')) | ~m1_subset_1(D_266, k2_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_66, c_129, c_4730])).
% 7.46/2.62  tff(c_4737, plain, (![D_266]: (r2_hidden(D_266, k2_struct_0('#skF_5')) | ~m1_subset_1(D_266, k2_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_74, c_4736])).
% 7.46/2.62  tff(c_4716, plain, (k2_orders_2('#skF_5', k1_xboole_0)=k2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4692, c_536])).
% 7.46/2.62  tff(c_48, plain, (![A_44, B_45]: (m1_subset_1(k2_orders_2(A_44, B_45), k1_zfmisc_1(u1_struct_0(A_44))) | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0(A_44))) | ~l1_orders_2(A_44) | ~v5_orders_2(A_44) | ~v4_orders_2(A_44) | ~v3_orders_2(A_44) | v2_struct_0(A_44))), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.46/2.62  tff(c_3261, plain, (![B_297, A_298, C_299, E_300]: (r2_orders_2(B_297, '#skF_3'(A_298, B_297, C_299), E_300) | ~r2_hidden(E_300, C_299) | ~m1_subset_1(E_300, u1_struct_0(B_297)) | ~r2_hidden(A_298, a_2_1_orders_2(B_297, C_299)) | ~m1_subset_1(C_299, k1_zfmisc_1(u1_struct_0(B_297))) | ~l1_orders_2(B_297) | ~v5_orders_2(B_297) | ~v4_orders_2(B_297) | ~v3_orders_2(B_297) | v2_struct_0(B_297))), inference(cnfTransformation, [status(thm)], [f_175])).
% 7.46/2.62  tff(c_6833, plain, (![A_460, A_461, B_462, E_463]: (r2_orders_2(A_460, '#skF_3'(A_461, A_460, k2_orders_2(A_460, B_462)), E_463) | ~r2_hidden(E_463, k2_orders_2(A_460, B_462)) | ~m1_subset_1(E_463, u1_struct_0(A_460)) | ~r2_hidden(A_461, a_2_1_orders_2(A_460, k2_orders_2(A_460, B_462))) | ~m1_subset_1(B_462, k1_zfmisc_1(u1_struct_0(A_460))) | ~l1_orders_2(A_460) | ~v5_orders_2(A_460) | ~v4_orders_2(A_460) | ~v3_orders_2(A_460) | v2_struct_0(A_460))), inference(resolution, [status(thm)], [c_48, c_3261])).
% 7.46/2.62  tff(c_6847, plain, (![A_461, E_463]: (r2_orders_2('#skF_5', '#skF_3'(A_461, '#skF_5', k2_struct_0('#skF_5')), E_463) | ~r2_hidden(E_463, k2_orders_2('#skF_5', k1_xboole_0)) | ~m1_subset_1(E_463, u1_struct_0('#skF_5')) | ~r2_hidden(A_461, a_2_1_orders_2('#skF_5', k2_orders_2('#skF_5', k1_xboole_0))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_4716, c_6833])).
% 7.46/2.62  tff(c_6861, plain, (![A_461, E_463]: (r2_orders_2('#skF_5', '#skF_3'(A_461, '#skF_5', k2_struct_0('#skF_5')), E_463) | ~r2_hidden(E_463, k2_struct_0('#skF_5')) | ~m1_subset_1(E_463, k2_struct_0('#skF_5')) | ~r2_hidden(A_461, a_2_1_orders_2('#skF_5', k2_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_66, c_22, c_129, c_4716, c_129, c_4716, c_6847])).
% 7.46/2.62  tff(c_6892, plain, (![A_465, E_466]: (r2_orders_2('#skF_5', '#skF_3'(A_465, '#skF_5', k2_struct_0('#skF_5')), E_466) | ~r2_hidden(E_466, k2_struct_0('#skF_5')) | ~m1_subset_1(E_466, k2_struct_0('#skF_5')) | ~r2_hidden(A_465, a_2_1_orders_2('#skF_5', k2_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_74, c_6861])).
% 7.46/2.62  tff(c_42, plain, (![A_34, C_40]: (~r2_orders_2(A_34, C_40, C_40) | ~m1_subset_1(C_40, u1_struct_0(A_34)) | ~l1_orders_2(A_34))), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.46/2.62  tff(c_6900, plain, (![A_465]: (~m1_subset_1('#skF_3'(A_465, '#skF_5', k2_struct_0('#skF_5')), u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~r2_hidden('#skF_3'(A_465, '#skF_5', k2_struct_0('#skF_5')), k2_struct_0('#skF_5')) | ~m1_subset_1('#skF_3'(A_465, '#skF_5', k2_struct_0('#skF_5')), k2_struct_0('#skF_5')) | ~r2_hidden(A_465, a_2_1_orders_2('#skF_5', k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_6892, c_42])).
% 7.46/2.62  tff(c_7076, plain, (![A_481]: (~r2_hidden('#skF_3'(A_481, '#skF_5', k2_struct_0('#skF_5')), k2_struct_0('#skF_5')) | ~m1_subset_1('#skF_3'(A_481, '#skF_5', k2_struct_0('#skF_5')), k2_struct_0('#skF_5')) | ~r2_hidden(A_481, a_2_1_orders_2('#skF_5', k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_129, c_6900])).
% 7.46/2.62  tff(c_7095, plain, (![A_482]: (~r2_hidden(A_482, a_2_1_orders_2('#skF_5', k2_struct_0('#skF_5'))) | ~m1_subset_1('#skF_3'(A_482, '#skF_5', k2_struct_0('#skF_5')), k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_4737, c_7076])).
% 7.46/2.62  tff(c_7105, plain, (![A_182]: (~r2_hidden(A_182, a_2_1_orders_2('#skF_5', k2_struct_0('#skF_5'))) | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_1236, c_7095])).
% 7.46/2.62  tff(c_7122, plain, (![A_483]: (~r2_hidden(A_483, a_2_1_orders_2('#skF_5', k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_207, c_7105])).
% 7.46/2.62  tff(c_7130, plain, (a_2_1_orders_2('#skF_5', k2_struct_0('#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_7122])).
% 7.46/2.62  tff(c_7136, plain, $false, inference(negUnitSimplification, [status(thm)], [c_541, c_7130])).
% 7.46/2.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.46/2.62  
% 7.46/2.62  Inference rules
% 7.46/2.62  ----------------------
% 7.46/2.62  #Ref     : 0
% 7.46/2.62  #Sup     : 1454
% 7.46/2.62  #Fact    : 0
% 7.46/2.62  #Define  : 0
% 7.46/2.62  #Split   : 34
% 7.46/2.62  #Chain   : 0
% 7.46/2.62  #Close   : 0
% 7.46/2.62  
% 7.46/2.62  Ordering : KBO
% 7.46/2.62  
% 7.46/2.62  Simplification rules
% 7.46/2.62  ----------------------
% 7.46/2.62  #Subsume      : 422
% 7.46/2.62  #Demod        : 2040
% 7.46/2.62  #Tautology    : 434
% 7.46/2.62  #SimpNegUnit  : 417
% 7.46/2.62  #BackRed      : 219
% 7.46/2.62  
% 7.46/2.62  #Partial instantiations: 0
% 7.46/2.62  #Strategies tried      : 1
% 7.46/2.62  
% 7.46/2.62  Timing (in seconds)
% 7.46/2.62  ----------------------
% 7.46/2.62  Preprocessing        : 0.35
% 7.46/2.62  Parsing              : 0.19
% 7.46/2.62  CNF conversion       : 0.03
% 7.46/2.62  Main loop            : 1.49
% 7.46/2.62  Inferencing          : 0.45
% 7.46/2.62  Reduction            : 0.54
% 7.46/2.62  Demodulation         : 0.36
% 7.46/2.62  BG Simplification    : 0.06
% 7.46/2.62  Subsumption          : 0.33
% 7.46/2.62  Abstraction          : 0.08
% 7.46/2.62  MUC search           : 0.00
% 7.46/2.62  Cooper               : 0.00
% 7.46/2.62  Total                : 1.88
% 7.46/2.62  Index Insertion      : 0.00
% 7.46/2.62  Index Deletion       : 0.00
% 7.46/2.62  Index Matching       : 0.00
% 7.46/2.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
