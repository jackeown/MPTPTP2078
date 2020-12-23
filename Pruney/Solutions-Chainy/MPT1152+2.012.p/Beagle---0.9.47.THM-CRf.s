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
% DateTime   : Thu Dec  3 10:19:29 EST 2020

% Result     : Theorem 5.52s
% Output     : CNFRefutation 5.52s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 509 expanded)
%              Number of leaves         :   38 ( 204 expanded)
%              Depth                    :   17
%              Number of atoms          :  215 (1356 expanded)
%              Number of equality atoms :   25 ( 258 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_159,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => k2_orders_2(A,k2_struct_0(A)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_orders_2)).

tff(f_118,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_99,axiom,(
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

tff(f_64,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_145,axiom,(
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

tff(f_114,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_orders_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_orders_2)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_83,axiom,(
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

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_55,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_52,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_50,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_48,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_46,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_30,plain,(
    ! [A_34] :
      ( l1_struct_0(A_34)
      | ~ l1_orders_2(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_67,plain,(
    ! [A_51] :
      ( u1_struct_0(A_51) = k2_struct_0(A_51)
      | ~ l1_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_73,plain,(
    ! [A_53] :
      ( u1_struct_0(A_53) = k2_struct_0(A_53)
      | ~ l1_orders_2(A_53) ) ),
    inference(resolution,[status(thm)],[c_30,c_67])).

tff(c_77,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_73])).

tff(c_224,plain,(
    ! [A_99,B_100] :
      ( k2_orders_2(A_99,B_100) = a_2_1_orders_2(A_99,B_100)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ l1_orders_2(A_99)
      | ~ v5_orders_2(A_99)
      | ~ v4_orders_2(A_99)
      | ~ v3_orders_2(A_99)
      | v2_struct_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_235,plain,(
    ! [B_100] :
      ( k2_orders_2('#skF_4',B_100) = a_2_1_orders_2('#skF_4',B_100)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_224])).

tff(c_243,plain,(
    ! [B_100] :
      ( k2_orders_2('#skF_4',B_100) = a_2_1_orders_2('#skF_4',B_100)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_235])).

tff(c_266,plain,(
    ! [B_103] :
      ( k2_orders_2('#skF_4',B_103) = a_2_1_orders_2('#skF_4',B_103)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_243])).

tff(c_281,plain,(
    k2_orders_2('#skF_4',k2_struct_0('#skF_4')) = a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_55,c_266])).

tff(c_44,plain,(
    k2_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_282,plain,(
    a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_44])).

tff(c_12,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_1'(A_11),A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_486,plain,(
    ! [A_118,B_119,C_120] :
      ( m1_subset_1('#skF_2'(A_118,B_119,C_120),u1_struct_0(B_119))
      | ~ r2_hidden(A_118,a_2_1_orders_2(B_119,C_120))
      | ~ m1_subset_1(C_120,k1_zfmisc_1(u1_struct_0(B_119)))
      | ~ l1_orders_2(B_119)
      | ~ v5_orders_2(B_119)
      | ~ v4_orders_2(B_119)
      | ~ v3_orders_2(B_119)
      | v2_struct_0(B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_491,plain,(
    ! [A_118,C_120] :
      ( m1_subset_1('#skF_2'(A_118,'#skF_4',C_120),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_118,a_2_1_orders_2('#skF_4',C_120))
      | ~ m1_subset_1(C_120,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_486])).

tff(c_494,plain,(
    ! [A_118,C_120] :
      ( m1_subset_1('#skF_2'(A_118,'#skF_4',C_120),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_118,a_2_1_orders_2('#skF_4',C_120))
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_77,c_491])).

tff(c_495,plain,(
    ! [A_118,C_120] :
      ( m1_subset_1('#skF_2'(A_118,'#skF_4',C_120),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_118,a_2_1_orders_2('#skF_4',C_120))
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_494])).

tff(c_295,plain,(
    ! [A_108,B_109] :
      ( m1_subset_1(k2_orders_2(A_108,B_109),k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_orders_2(A_108)
      | ~ v5_orders_2(A_108)
      | ~ v4_orders_2(A_108)
      | ~ v3_orders_2(A_108)
      | v2_struct_0(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_305,plain,
    ( m1_subset_1(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_295])).

tff(c_313,plain,
    ( m1_subset_1(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_55,c_77,c_77,c_305])).

tff(c_314,plain,(
    m1_subset_1(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_313])).

tff(c_10,plain,(
    ! [C_10,B_9,A_8] :
      ( ~ v1_xboole_0(C_10)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(C_10))
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_327,plain,(
    ! [A_8] :
      ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_8,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_314,c_10])).

tff(c_328,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_327])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1017,plain,(
    ! [B_154,A_155,C_156,E_157] :
      ( r2_orders_2(B_154,'#skF_2'(A_155,B_154,C_156),E_157)
      | ~ r2_hidden(E_157,C_156)
      | ~ m1_subset_1(E_157,u1_struct_0(B_154))
      | ~ r2_hidden(A_155,a_2_1_orders_2(B_154,C_156))
      | ~ m1_subset_1(C_156,k1_zfmisc_1(u1_struct_0(B_154)))
      | ~ l1_orders_2(B_154)
      | ~ v5_orders_2(B_154)
      | ~ v4_orders_2(B_154)
      | ~ v3_orders_2(B_154)
      | v2_struct_0(B_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_2182,plain,(
    ! [B_210,A_211,E_212] :
      ( r2_orders_2(B_210,'#skF_2'(A_211,B_210,u1_struct_0(B_210)),E_212)
      | ~ r2_hidden(E_212,u1_struct_0(B_210))
      | ~ m1_subset_1(E_212,u1_struct_0(B_210))
      | ~ r2_hidden(A_211,a_2_1_orders_2(B_210,u1_struct_0(B_210)))
      | ~ l1_orders_2(B_210)
      | ~ v5_orders_2(B_210)
      | ~ v4_orders_2(B_210)
      | ~ v3_orders_2(B_210)
      | v2_struct_0(B_210) ) ),
    inference(resolution,[status(thm)],[c_55,c_1017])).

tff(c_2193,plain,(
    ! [A_211,E_212] :
      ( r2_orders_2('#skF_4','#skF_2'(A_211,'#skF_4',k2_struct_0('#skF_4')),E_212)
      | ~ r2_hidden(E_212,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_212,u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_211,a_2_1_orders_2('#skF_4',u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_2182])).

tff(c_2198,plain,(
    ! [A_211,E_212] :
      ( r2_orders_2('#skF_4','#skF_2'(A_211,'#skF_4',k2_struct_0('#skF_4')),E_212)
      | ~ r2_hidden(E_212,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_212,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_211,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_77,c_77,c_77,c_2193])).

tff(c_2640,plain,(
    ! [A_256,E_257] :
      ( r2_orders_2('#skF_4','#skF_2'(A_256,'#skF_4',k2_struct_0('#skF_4')),E_257)
      | ~ r2_hidden(E_257,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_257,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_256,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2198])).

tff(c_22,plain,(
    ! [A_22,C_28] :
      ( ~ r2_orders_2(A_22,C_28,C_28)
      | ~ m1_subset_1(C_28,u1_struct_0(A_22))
      | ~ l1_orders_2(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2648,plain,(
    ! [A_256] :
      ( ~ m1_subset_1('#skF_2'(A_256,'#skF_4',k2_struct_0('#skF_4')),u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ r2_hidden('#skF_2'(A_256,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_256,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_256,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_2640,c_22])).

tff(c_3506,plain,(
    ! [A_295] :
      ( ~ r2_hidden('#skF_2'(A_295,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_295,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_295,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_77,c_2648])).

tff(c_3515,plain,(
    ! [A_295] :
      ( ~ r2_hidden(A_295,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_295,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_6,c_3506])).

tff(c_3521,plain,(
    ! [A_296] :
      ( ~ r2_hidden(A_296,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_2'(A_296,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_328,c_3515])).

tff(c_3531,plain,(
    ! [A_118] :
      ( ~ r2_hidden(A_118,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_495,c_3521])).

tff(c_3542,plain,(
    ! [A_297] : ~ r2_hidden(A_297,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_3531])).

tff(c_3550,plain,(
    a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_3542])).

tff(c_3557,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_282,c_3550])).

tff(c_3559,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_327])).

tff(c_83,plain,(
    ! [C_56,B_57,A_58] :
      ( ~ v1_xboole_0(C_56)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(C_56))
      | ~ r2_hidden(A_58,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_91,plain,(
    ! [A_62,A_63] :
      ( ~ v1_xboole_0(A_62)
      | ~ r2_hidden(A_63,A_62) ) ),
    inference(resolution,[status(thm)],[c_55,c_83])).

tff(c_99,plain,(
    ! [A_11] :
      ( ~ v1_xboole_0(A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(resolution,[status(thm)],[c_12,c_91])).

tff(c_3563,plain,(
    k2_struct_0('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3559,c_99])).

tff(c_3575,plain,(
    a_2_1_orders_2('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3563,c_282])).

tff(c_3558,plain,(
    ! [A_8] : ~ r2_hidden(A_8,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_327])).

tff(c_3627,plain,(
    ! [A_302] : ~ r2_hidden(A_302,a_2_1_orders_2('#skF_4',k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3563,c_3558])).

tff(c_3635,plain,(
    a_2_1_orders_2('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_3627])).

tff(c_3640,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3575,c_3635])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:14:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.52/2.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.52/2.14  
% 5.52/2.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.52/2.14  %$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k4_tarski > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3
% 5.52/2.14  
% 5.52/2.14  %Foreground sorts:
% 5.52/2.14  
% 5.52/2.14  
% 5.52/2.14  %Background operators:
% 5.52/2.14  
% 5.52/2.14  
% 5.52/2.14  %Foreground operators:
% 5.52/2.14  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.52/2.14  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 5.52/2.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.52/2.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.52/2.14  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.52/2.14  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.52/2.14  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 5.52/2.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.52/2.14  tff(a_2_1_orders_2, type, a_2_1_orders_2: ($i * $i) > $i).
% 5.52/2.14  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 5.52/2.14  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.52/2.14  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 5.52/2.14  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 5.52/2.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.52/2.14  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.52/2.14  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 5.52/2.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.52/2.14  tff('#skF_4', type, '#skF_4': $i).
% 5.52/2.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.52/2.14  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 5.52/2.14  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 5.52/2.14  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.52/2.14  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 5.52/2.14  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 5.52/2.14  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.52/2.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.52/2.14  
% 5.52/2.15  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 5.52/2.15  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 5.52/2.15  tff(f_159, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k2_orders_2(A, k2_struct_0(A)) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_orders_2)).
% 5.52/2.15  tff(f_118, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 5.52/2.15  tff(f_68, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 5.52/2.15  tff(f_99, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_orders_2(A, B) = a_2_1_orders_2(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_orders_2)).
% 5.52/2.15  tff(f_64, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 5.52/2.15  tff(f_145, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_1_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, D, E))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_1_orders_2)).
% 5.52/2.15  tff(f_114, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_orders_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_orders_2)).
% 5.52/2.15  tff(f_48, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 5.52/2.15  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 5.52/2.15  tff(f_83, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_orders_2)).
% 5.52/2.15  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.52/2.15  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.52/2.15  tff(c_55, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 5.52/2.15  tff(c_54, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_159])).
% 5.52/2.15  tff(c_52, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_159])).
% 5.52/2.15  tff(c_50, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_159])).
% 5.52/2.15  tff(c_48, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_159])).
% 5.52/2.15  tff(c_46, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_159])).
% 5.52/2.15  tff(c_30, plain, (![A_34]: (l1_struct_0(A_34) | ~l1_orders_2(A_34))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.52/2.15  tff(c_67, plain, (![A_51]: (u1_struct_0(A_51)=k2_struct_0(A_51) | ~l1_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.52/2.15  tff(c_73, plain, (![A_53]: (u1_struct_0(A_53)=k2_struct_0(A_53) | ~l1_orders_2(A_53))), inference(resolution, [status(thm)], [c_30, c_67])).
% 5.52/2.15  tff(c_77, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_46, c_73])).
% 5.52/2.15  tff(c_224, plain, (![A_99, B_100]: (k2_orders_2(A_99, B_100)=a_2_1_orders_2(A_99, B_100) | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(A_99))) | ~l1_orders_2(A_99) | ~v5_orders_2(A_99) | ~v4_orders_2(A_99) | ~v3_orders_2(A_99) | v2_struct_0(A_99))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.52/2.15  tff(c_235, plain, (![B_100]: (k2_orders_2('#skF_4', B_100)=a_2_1_orders_2('#skF_4', B_100) | ~m1_subset_1(B_100, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_77, c_224])).
% 5.52/2.15  tff(c_243, plain, (![B_100]: (k2_orders_2('#skF_4', B_100)=a_2_1_orders_2('#skF_4', B_100) | ~m1_subset_1(B_100, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_235])).
% 5.52/2.15  tff(c_266, plain, (![B_103]: (k2_orders_2('#skF_4', B_103)=a_2_1_orders_2('#skF_4', B_103) | ~m1_subset_1(B_103, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_243])).
% 5.52/2.15  tff(c_281, plain, (k2_orders_2('#skF_4', k2_struct_0('#skF_4'))=a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_55, c_266])).
% 5.52/2.15  tff(c_44, plain, (k2_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_159])).
% 5.52/2.15  tff(c_282, plain, (a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_281, c_44])).
% 5.52/2.15  tff(c_12, plain, (![A_11]: (r2_hidden('#skF_1'(A_11), A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.52/2.15  tff(c_486, plain, (![A_118, B_119, C_120]: (m1_subset_1('#skF_2'(A_118, B_119, C_120), u1_struct_0(B_119)) | ~r2_hidden(A_118, a_2_1_orders_2(B_119, C_120)) | ~m1_subset_1(C_120, k1_zfmisc_1(u1_struct_0(B_119))) | ~l1_orders_2(B_119) | ~v5_orders_2(B_119) | ~v4_orders_2(B_119) | ~v3_orders_2(B_119) | v2_struct_0(B_119))), inference(cnfTransformation, [status(thm)], [f_145])).
% 5.52/2.15  tff(c_491, plain, (![A_118, C_120]: (m1_subset_1('#skF_2'(A_118, '#skF_4', C_120), k2_struct_0('#skF_4')) | ~r2_hidden(A_118, a_2_1_orders_2('#skF_4', C_120)) | ~m1_subset_1(C_120, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_77, c_486])).
% 5.52/2.15  tff(c_494, plain, (![A_118, C_120]: (m1_subset_1('#skF_2'(A_118, '#skF_4', C_120), k2_struct_0('#skF_4')) | ~r2_hidden(A_118, a_2_1_orders_2('#skF_4', C_120)) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_77, c_491])).
% 5.52/2.15  tff(c_495, plain, (![A_118, C_120]: (m1_subset_1('#skF_2'(A_118, '#skF_4', C_120), k2_struct_0('#skF_4')) | ~r2_hidden(A_118, a_2_1_orders_2('#skF_4', C_120)) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_494])).
% 5.52/2.15  tff(c_295, plain, (![A_108, B_109]: (m1_subset_1(k2_orders_2(A_108, B_109), k1_zfmisc_1(u1_struct_0(A_108))) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_orders_2(A_108) | ~v5_orders_2(A_108) | ~v4_orders_2(A_108) | ~v3_orders_2(A_108) | v2_struct_0(A_108))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.52/2.15  tff(c_305, plain, (m1_subset_1(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_281, c_295])).
% 5.52/2.15  tff(c_313, plain, (m1_subset_1(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')), k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_55, c_77, c_77, c_305])).
% 5.52/2.15  tff(c_314, plain, (m1_subset_1(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_54, c_313])).
% 5.52/2.15  tff(c_10, plain, (![C_10, B_9, A_8]: (~v1_xboole_0(C_10) | ~m1_subset_1(B_9, k1_zfmisc_1(C_10)) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.52/2.15  tff(c_327, plain, (![A_8]: (~v1_xboole_0(k2_struct_0('#skF_4')) | ~r2_hidden(A_8, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_314, c_10])).
% 5.52/2.15  tff(c_328, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_327])).
% 5.52/2.15  tff(c_6, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.52/2.15  tff(c_1017, plain, (![B_154, A_155, C_156, E_157]: (r2_orders_2(B_154, '#skF_2'(A_155, B_154, C_156), E_157) | ~r2_hidden(E_157, C_156) | ~m1_subset_1(E_157, u1_struct_0(B_154)) | ~r2_hidden(A_155, a_2_1_orders_2(B_154, C_156)) | ~m1_subset_1(C_156, k1_zfmisc_1(u1_struct_0(B_154))) | ~l1_orders_2(B_154) | ~v5_orders_2(B_154) | ~v4_orders_2(B_154) | ~v3_orders_2(B_154) | v2_struct_0(B_154))), inference(cnfTransformation, [status(thm)], [f_145])).
% 5.52/2.15  tff(c_2182, plain, (![B_210, A_211, E_212]: (r2_orders_2(B_210, '#skF_2'(A_211, B_210, u1_struct_0(B_210)), E_212) | ~r2_hidden(E_212, u1_struct_0(B_210)) | ~m1_subset_1(E_212, u1_struct_0(B_210)) | ~r2_hidden(A_211, a_2_1_orders_2(B_210, u1_struct_0(B_210))) | ~l1_orders_2(B_210) | ~v5_orders_2(B_210) | ~v4_orders_2(B_210) | ~v3_orders_2(B_210) | v2_struct_0(B_210))), inference(resolution, [status(thm)], [c_55, c_1017])).
% 5.52/2.15  tff(c_2193, plain, (![A_211, E_212]: (r2_orders_2('#skF_4', '#skF_2'(A_211, '#skF_4', k2_struct_0('#skF_4')), E_212) | ~r2_hidden(E_212, u1_struct_0('#skF_4')) | ~m1_subset_1(E_212, u1_struct_0('#skF_4')) | ~r2_hidden(A_211, a_2_1_orders_2('#skF_4', u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_77, c_2182])).
% 5.52/2.15  tff(c_2198, plain, (![A_211, E_212]: (r2_orders_2('#skF_4', '#skF_2'(A_211, '#skF_4', k2_struct_0('#skF_4')), E_212) | ~r2_hidden(E_212, k2_struct_0('#skF_4')) | ~m1_subset_1(E_212, k2_struct_0('#skF_4')) | ~r2_hidden(A_211, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_77, c_77, c_77, c_2193])).
% 5.52/2.15  tff(c_2640, plain, (![A_256, E_257]: (r2_orders_2('#skF_4', '#skF_2'(A_256, '#skF_4', k2_struct_0('#skF_4')), E_257) | ~r2_hidden(E_257, k2_struct_0('#skF_4')) | ~m1_subset_1(E_257, k2_struct_0('#skF_4')) | ~r2_hidden(A_256, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_2198])).
% 5.52/2.15  tff(c_22, plain, (![A_22, C_28]: (~r2_orders_2(A_22, C_28, C_28) | ~m1_subset_1(C_28, u1_struct_0(A_22)) | ~l1_orders_2(A_22))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.52/2.15  tff(c_2648, plain, (![A_256]: (~m1_subset_1('#skF_2'(A_256, '#skF_4', k2_struct_0('#skF_4')), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~r2_hidden('#skF_2'(A_256, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(A_256, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~r2_hidden(A_256, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_2640, c_22])).
% 5.52/2.15  tff(c_3506, plain, (![A_295]: (~r2_hidden('#skF_2'(A_295, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(A_295, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~r2_hidden(A_295, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_77, c_2648])).
% 5.52/2.15  tff(c_3515, plain, (![A_295]: (~r2_hidden(A_295, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(A_295, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_6, c_3506])).
% 5.52/2.15  tff(c_3521, plain, (![A_296]: (~r2_hidden(A_296, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~m1_subset_1('#skF_2'(A_296, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_328, c_3515])).
% 5.52/2.15  tff(c_3531, plain, (![A_118]: (~r2_hidden(A_118, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_495, c_3521])).
% 5.52/2.15  tff(c_3542, plain, (![A_297]: (~r2_hidden(A_297, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_3531])).
% 5.52/2.15  tff(c_3550, plain, (a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_3542])).
% 5.52/2.15  tff(c_3557, plain, $false, inference(negUnitSimplification, [status(thm)], [c_282, c_3550])).
% 5.52/2.15  tff(c_3559, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_327])).
% 5.52/2.15  tff(c_83, plain, (![C_56, B_57, A_58]: (~v1_xboole_0(C_56) | ~m1_subset_1(B_57, k1_zfmisc_1(C_56)) | ~r2_hidden(A_58, B_57))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.52/2.15  tff(c_91, plain, (![A_62, A_63]: (~v1_xboole_0(A_62) | ~r2_hidden(A_63, A_62))), inference(resolution, [status(thm)], [c_55, c_83])).
% 5.52/2.15  tff(c_99, plain, (![A_11]: (~v1_xboole_0(A_11) | k1_xboole_0=A_11)), inference(resolution, [status(thm)], [c_12, c_91])).
% 5.52/2.15  tff(c_3563, plain, (k2_struct_0('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_3559, c_99])).
% 5.52/2.15  tff(c_3575, plain, (a_2_1_orders_2('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3563, c_282])).
% 5.52/2.15  tff(c_3558, plain, (![A_8]: (~r2_hidden(A_8, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(splitRight, [status(thm)], [c_327])).
% 5.52/2.15  tff(c_3627, plain, (![A_302]: (~r2_hidden(A_302, a_2_1_orders_2('#skF_4', k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_3563, c_3558])).
% 5.52/2.15  tff(c_3635, plain, (a_2_1_orders_2('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_3627])).
% 5.52/2.15  tff(c_3640, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3575, c_3635])).
% 5.52/2.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.52/2.15  
% 5.52/2.15  Inference rules
% 5.52/2.15  ----------------------
% 5.52/2.15  #Ref     : 0
% 5.52/2.15  #Sup     : 764
% 5.52/2.15  #Fact    : 0
% 5.52/2.15  #Define  : 0
% 5.52/2.15  #Split   : 19
% 5.52/2.15  #Chain   : 0
% 5.52/2.15  #Close   : 0
% 5.52/2.15  
% 5.52/2.15  Ordering : KBO
% 5.52/2.15  
% 5.52/2.15  Simplification rules
% 5.52/2.15  ----------------------
% 5.52/2.15  #Subsume      : 252
% 5.52/2.15  #Demod        : 1292
% 5.52/2.15  #Tautology    : 196
% 5.52/2.15  #SimpNegUnit  : 247
% 5.52/2.15  #BackRed      : 112
% 5.52/2.15  
% 5.52/2.15  #Partial instantiations: 0
% 5.52/2.15  #Strategies tried      : 1
% 5.52/2.15  
% 5.52/2.15  Timing (in seconds)
% 5.52/2.15  ----------------------
% 5.52/2.16  Preprocessing        : 0.32
% 5.52/2.16  Parsing              : 0.16
% 5.52/2.16  CNF conversion       : 0.02
% 5.52/2.16  Main loop            : 0.99
% 5.52/2.16  Inferencing          : 0.31
% 5.52/2.16  Reduction            : 0.34
% 5.52/2.16  Demodulation         : 0.23
% 5.52/2.16  BG Simplification    : 0.05
% 5.52/2.16  Subsumption          : 0.21
% 5.52/2.16  Abstraction          : 0.05
% 5.52/2.16  MUC search           : 0.00
% 5.52/2.16  Cooper               : 0.00
% 5.52/2.16  Total                : 1.34
% 5.52/2.16  Index Insertion      : 0.00
% 5.52/2.16  Index Deletion       : 0.00
% 5.52/2.16  Index Matching       : 0.00
% 5.52/2.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
