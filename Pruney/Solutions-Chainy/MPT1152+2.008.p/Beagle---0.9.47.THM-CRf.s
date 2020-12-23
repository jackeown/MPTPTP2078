%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:28 EST 2020

% Result     : Theorem 4.51s
% Output     : CNFRefutation 4.51s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 493 expanded)
%              Number of leaves         :   38 ( 198 expanded)
%              Depth                    :   17
%              Number of atoms          :  213 (1318 expanded)
%              Number of equality atoms :   25 ( 248 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k3_mcart_1 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_153,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => k2_orders_2(A,k2_struct_0(A)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_orders_2)).

tff(f_112,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_93,axiom,(
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

tff(f_58,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_139,axiom,(
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

tff(f_108,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_orders_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_orders_2)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_77,axiom,(
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

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_53,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_50,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_48,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_46,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_44,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_28,plain,(
    ! [A_35] :
      ( l1_struct_0(A_35)
      | ~ l1_orders_2(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_66,plain,(
    ! [A_53] :
      ( u1_struct_0(A_53) = k2_struct_0(A_53)
      | ~ l1_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_71,plain,(
    ! [A_54] :
      ( u1_struct_0(A_54) = k2_struct_0(A_54)
      | ~ l1_orders_2(A_54) ) ),
    inference(resolution,[status(thm)],[c_28,c_66])).

tff(c_75,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_71])).

tff(c_121,plain,(
    ! [A_95,B_96] :
      ( k2_orders_2(A_95,B_96) = a_2_1_orders_2(A_95,B_96)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_orders_2(A_95)
      | ~ v5_orders_2(A_95)
      | ~ v4_orders_2(A_95)
      | ~ v3_orders_2(A_95)
      | v2_struct_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_124,plain,(
    ! [B_96] :
      ( k2_orders_2('#skF_4',B_96) = a_2_1_orders_2('#skF_4',B_96)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_121])).

tff(c_130,plain,(
    ! [B_96] :
      ( k2_orders_2('#skF_4',B_96) = a_2_1_orders_2('#skF_4',B_96)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_124])).

tff(c_133,plain,(
    ! [B_97] :
      ( k2_orders_2('#skF_4',B_97) = a_2_1_orders_2('#skF_4',B_97)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_130])).

tff(c_138,plain,(
    k2_orders_2('#skF_4',k2_struct_0('#skF_4')) = a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_53,c_133])).

tff(c_42,plain,(
    k2_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_139,plain,(
    a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_42])).

tff(c_10,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_1'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_291,plain,(
    ! [A_106,B_107,C_108] :
      ( m1_subset_1('#skF_2'(A_106,B_107,C_108),u1_struct_0(B_107))
      | ~ r2_hidden(A_106,a_2_1_orders_2(B_107,C_108))
      | ~ m1_subset_1(C_108,k1_zfmisc_1(u1_struct_0(B_107)))
      | ~ l1_orders_2(B_107)
      | ~ v5_orders_2(B_107)
      | ~ v4_orders_2(B_107)
      | ~ v3_orders_2(B_107)
      | v2_struct_0(B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_296,plain,(
    ! [A_106,C_108] :
      ( m1_subset_1('#skF_2'(A_106,'#skF_4',C_108),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_106,a_2_1_orders_2('#skF_4',C_108))
      | ~ m1_subset_1(C_108,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_291])).

tff(c_299,plain,(
    ! [A_106,C_108] :
      ( m1_subset_1('#skF_2'(A_106,'#skF_4',C_108),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_106,a_2_1_orders_2('#skF_4',C_108))
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_75,c_296])).

tff(c_300,plain,(
    ! [A_106,C_108] :
      ( m1_subset_1('#skF_2'(A_106,'#skF_4',C_108),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_106,a_2_1_orders_2('#skF_4',C_108))
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_299])).

tff(c_159,plain,(
    ! [A_99,B_100] :
      ( m1_subset_1(k2_orders_2(A_99,B_100),k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ l1_orders_2(A_99)
      | ~ v5_orders_2(A_99)
      | ~ v4_orders_2(A_99)
      | ~ v3_orders_2(A_99)
      | v2_struct_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_170,plain,
    ( m1_subset_1(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_159])).

tff(c_179,plain,
    ( m1_subset_1(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_53,c_75,c_75,c_170])).

tff(c_180,plain,(
    m1_subset_1(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_179])).

tff(c_8,plain,(
    ! [C_7,B_6,A_5] :
      ( ~ v1_xboole_0(C_7)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(C_7))
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_190,plain,(
    ! [A_5] :
      ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_5,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_180,c_8])).

tff(c_191,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_190])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1929,plain,(
    ! [B_192,A_193,C_194,E_195] :
      ( r2_orders_2(B_192,'#skF_2'(A_193,B_192,C_194),E_195)
      | ~ r2_hidden(E_195,C_194)
      | ~ m1_subset_1(E_195,u1_struct_0(B_192))
      | ~ r2_hidden(A_193,a_2_1_orders_2(B_192,C_194))
      | ~ m1_subset_1(C_194,k1_zfmisc_1(u1_struct_0(B_192)))
      | ~ l1_orders_2(B_192)
      | ~ v5_orders_2(B_192)
      | ~ v4_orders_2(B_192)
      | ~ v3_orders_2(B_192)
      | v2_struct_0(B_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1935,plain,(
    ! [A_193,C_194,E_195] :
      ( r2_orders_2('#skF_4','#skF_2'(A_193,'#skF_4',C_194),E_195)
      | ~ r2_hidden(E_195,C_194)
      | ~ m1_subset_1(E_195,u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_193,a_2_1_orders_2('#skF_4',C_194))
      | ~ m1_subset_1(C_194,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_1929])).

tff(c_1942,plain,(
    ! [A_193,C_194,E_195] :
      ( r2_orders_2('#skF_4','#skF_2'(A_193,'#skF_4',C_194),E_195)
      | ~ r2_hidden(E_195,C_194)
      | ~ m1_subset_1(E_195,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_193,a_2_1_orders_2('#skF_4',C_194))
      | ~ m1_subset_1(C_194,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_75,c_1935])).

tff(c_1946,plain,(
    ! [A_196,C_197,E_198] :
      ( r2_orders_2('#skF_4','#skF_2'(A_196,'#skF_4',C_197),E_198)
      | ~ r2_hidden(E_198,C_197)
      | ~ m1_subset_1(E_198,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_196,a_2_1_orders_2('#skF_4',C_197))
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1942])).

tff(c_1995,plain,(
    ! [A_200,E_201] :
      ( r2_orders_2('#skF_4','#skF_2'(A_200,'#skF_4',k2_struct_0('#skF_4')),E_201)
      | ~ r2_hidden(E_201,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_201,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_200,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_53,c_1946])).

tff(c_20,plain,(
    ! [A_23,C_29] :
      ( ~ r2_orders_2(A_23,C_29,C_29)
      | ~ m1_subset_1(C_29,u1_struct_0(A_23))
      | ~ l1_orders_2(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2003,plain,(
    ! [A_200] :
      ( ~ m1_subset_1('#skF_2'(A_200,'#skF_4',k2_struct_0('#skF_4')),u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ r2_hidden('#skF_2'(A_200,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_200,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_200,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_1995,c_20])).

tff(c_2017,plain,(
    ! [A_202] :
      ( ~ r2_hidden('#skF_2'(A_202,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_202,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_202,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_75,c_2003])).

tff(c_2023,plain,(
    ! [A_202] :
      ( ~ r2_hidden(A_202,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_202,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_6,c_2017])).

tff(c_2027,plain,(
    ! [A_203] :
      ( ~ r2_hidden(A_203,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_2'(A_203,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_191,c_2023])).

tff(c_2034,plain,(
    ! [A_106] :
      ( ~ r2_hidden(A_106,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_300,c_2027])).

tff(c_2042,plain,(
    ! [A_204] : ~ r2_hidden(A_204,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_2034])).

tff(c_2050,plain,(
    a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_2042])).

tff(c_2057,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_2050])).

tff(c_2059,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_190])).

tff(c_81,plain,(
    ! [C_57,B_58,A_59] :
      ( ~ v1_xboole_0(C_57)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(C_57))
      | ~ r2_hidden(A_59,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_86,plain,(
    ! [A_62,A_63] :
      ( ~ v1_xboole_0(A_62)
      | ~ r2_hidden(A_63,A_62) ) ),
    inference(resolution,[status(thm)],[c_53,c_81])).

tff(c_94,plain,(
    ! [A_8] :
      ( ~ v1_xboole_0(A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(resolution,[status(thm)],[c_10,c_86])).

tff(c_2063,plain,(
    k2_struct_0('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2059,c_94])).

tff(c_2075,plain,(
    a_2_1_orders_2('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2063,c_139])).

tff(c_2058,plain,(
    ! [A_5] : ~ r2_hidden(A_5,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_190])).

tff(c_2126,plain,(
    ! [A_208] : ~ r2_hidden(A_208,a_2_1_orders_2('#skF_4',k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2063,c_2058])).

tff(c_2134,plain,(
    a_2_1_orders_2('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_2126])).

tff(c_2139,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2075,c_2134])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:38:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.51/1.87  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.51/1.88  
% 4.51/1.88  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.51/1.88  %$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k3_mcart_1 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3
% 4.51/1.88  
% 4.51/1.88  %Foreground sorts:
% 4.51/1.88  
% 4.51/1.88  
% 4.51/1.88  %Background operators:
% 4.51/1.88  
% 4.51/1.88  
% 4.51/1.88  %Foreground operators:
% 4.51/1.88  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.51/1.88  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 4.51/1.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.51/1.88  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.51/1.88  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.51/1.88  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 4.51/1.88  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.51/1.88  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 4.51/1.88  tff(a_2_1_orders_2, type, a_2_1_orders_2: ($i * $i) > $i).
% 4.51/1.88  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 4.51/1.88  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.51/1.88  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 4.51/1.88  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 4.51/1.88  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.51/1.88  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.51/1.88  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 4.51/1.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.51/1.88  tff('#skF_4', type, '#skF_4': $i).
% 4.51/1.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.51/1.88  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 4.51/1.88  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 4.51/1.88  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.51/1.88  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.51/1.88  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.51/1.88  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.51/1.88  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.51/1.88  
% 4.51/1.89  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 4.51/1.89  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.51/1.89  tff(f_153, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k2_orders_2(A, k2_struct_0(A)) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_orders_2)).
% 4.51/1.89  tff(f_112, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 4.51/1.89  tff(f_62, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 4.51/1.89  tff(f_93, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_orders_2(A, B) = a_2_1_orders_2(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_orders_2)).
% 4.51/1.89  tff(f_58, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_mcart_1)).
% 4.51/1.89  tff(f_139, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_1_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, D, E))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_1_orders_2)).
% 4.51/1.89  tff(f_108, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_orders_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_orders_2)).
% 4.51/1.89  tff(f_42, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 4.51/1.89  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 4.51/1.89  tff(f_77, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_orders_2)).
% 4.51/1.89  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.51/1.89  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.51/1.89  tff(c_53, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 4.51/1.89  tff(c_52, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_153])).
% 4.51/1.89  tff(c_50, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_153])).
% 4.51/1.89  tff(c_48, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_153])).
% 4.51/1.89  tff(c_46, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_153])).
% 4.51/1.89  tff(c_44, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_153])).
% 4.51/1.89  tff(c_28, plain, (![A_35]: (l1_struct_0(A_35) | ~l1_orders_2(A_35))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.51/1.89  tff(c_66, plain, (![A_53]: (u1_struct_0(A_53)=k2_struct_0(A_53) | ~l1_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.51/1.89  tff(c_71, plain, (![A_54]: (u1_struct_0(A_54)=k2_struct_0(A_54) | ~l1_orders_2(A_54))), inference(resolution, [status(thm)], [c_28, c_66])).
% 4.51/1.89  tff(c_75, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_44, c_71])).
% 4.51/1.89  tff(c_121, plain, (![A_95, B_96]: (k2_orders_2(A_95, B_96)=a_2_1_orders_2(A_95, B_96) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_orders_2(A_95) | ~v5_orders_2(A_95) | ~v4_orders_2(A_95) | ~v3_orders_2(A_95) | v2_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.51/1.89  tff(c_124, plain, (![B_96]: (k2_orders_2('#skF_4', B_96)=a_2_1_orders_2('#skF_4', B_96) | ~m1_subset_1(B_96, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_75, c_121])).
% 4.51/1.89  tff(c_130, plain, (![B_96]: (k2_orders_2('#skF_4', B_96)=a_2_1_orders_2('#skF_4', B_96) | ~m1_subset_1(B_96, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_124])).
% 4.51/1.89  tff(c_133, plain, (![B_97]: (k2_orders_2('#skF_4', B_97)=a_2_1_orders_2('#skF_4', B_97) | ~m1_subset_1(B_97, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_52, c_130])).
% 4.51/1.89  tff(c_138, plain, (k2_orders_2('#skF_4', k2_struct_0('#skF_4'))=a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_53, c_133])).
% 4.51/1.89  tff(c_42, plain, (k2_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_153])).
% 4.51/1.89  tff(c_139, plain, (a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_138, c_42])).
% 4.51/1.89  tff(c_10, plain, (![A_8]: (r2_hidden('#skF_1'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.51/1.89  tff(c_291, plain, (![A_106, B_107, C_108]: (m1_subset_1('#skF_2'(A_106, B_107, C_108), u1_struct_0(B_107)) | ~r2_hidden(A_106, a_2_1_orders_2(B_107, C_108)) | ~m1_subset_1(C_108, k1_zfmisc_1(u1_struct_0(B_107))) | ~l1_orders_2(B_107) | ~v5_orders_2(B_107) | ~v4_orders_2(B_107) | ~v3_orders_2(B_107) | v2_struct_0(B_107))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.51/1.89  tff(c_296, plain, (![A_106, C_108]: (m1_subset_1('#skF_2'(A_106, '#skF_4', C_108), k2_struct_0('#skF_4')) | ~r2_hidden(A_106, a_2_1_orders_2('#skF_4', C_108)) | ~m1_subset_1(C_108, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_75, c_291])).
% 4.51/1.89  tff(c_299, plain, (![A_106, C_108]: (m1_subset_1('#skF_2'(A_106, '#skF_4', C_108), k2_struct_0('#skF_4')) | ~r2_hidden(A_106, a_2_1_orders_2('#skF_4', C_108)) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_75, c_296])).
% 4.51/1.89  tff(c_300, plain, (![A_106, C_108]: (m1_subset_1('#skF_2'(A_106, '#skF_4', C_108), k2_struct_0('#skF_4')) | ~r2_hidden(A_106, a_2_1_orders_2('#skF_4', C_108)) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_52, c_299])).
% 4.51/1.89  tff(c_159, plain, (![A_99, B_100]: (m1_subset_1(k2_orders_2(A_99, B_100), k1_zfmisc_1(u1_struct_0(A_99))) | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(A_99))) | ~l1_orders_2(A_99) | ~v5_orders_2(A_99) | ~v4_orders_2(A_99) | ~v3_orders_2(A_99) | v2_struct_0(A_99))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.51/1.89  tff(c_170, plain, (m1_subset_1(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_138, c_159])).
% 4.51/1.89  tff(c_179, plain, (m1_subset_1(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')), k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_53, c_75, c_75, c_170])).
% 4.51/1.89  tff(c_180, plain, (m1_subset_1(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_52, c_179])).
% 4.51/1.89  tff(c_8, plain, (![C_7, B_6, A_5]: (~v1_xboole_0(C_7) | ~m1_subset_1(B_6, k1_zfmisc_1(C_7)) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.51/1.89  tff(c_190, plain, (![A_5]: (~v1_xboole_0(k2_struct_0('#skF_4')) | ~r2_hidden(A_5, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_180, c_8])).
% 4.51/1.89  tff(c_191, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_190])).
% 4.51/1.89  tff(c_6, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.51/1.89  tff(c_1929, plain, (![B_192, A_193, C_194, E_195]: (r2_orders_2(B_192, '#skF_2'(A_193, B_192, C_194), E_195) | ~r2_hidden(E_195, C_194) | ~m1_subset_1(E_195, u1_struct_0(B_192)) | ~r2_hidden(A_193, a_2_1_orders_2(B_192, C_194)) | ~m1_subset_1(C_194, k1_zfmisc_1(u1_struct_0(B_192))) | ~l1_orders_2(B_192) | ~v5_orders_2(B_192) | ~v4_orders_2(B_192) | ~v3_orders_2(B_192) | v2_struct_0(B_192))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.51/1.89  tff(c_1935, plain, (![A_193, C_194, E_195]: (r2_orders_2('#skF_4', '#skF_2'(A_193, '#skF_4', C_194), E_195) | ~r2_hidden(E_195, C_194) | ~m1_subset_1(E_195, u1_struct_0('#skF_4')) | ~r2_hidden(A_193, a_2_1_orders_2('#skF_4', C_194)) | ~m1_subset_1(C_194, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_75, c_1929])).
% 4.51/1.89  tff(c_1942, plain, (![A_193, C_194, E_195]: (r2_orders_2('#skF_4', '#skF_2'(A_193, '#skF_4', C_194), E_195) | ~r2_hidden(E_195, C_194) | ~m1_subset_1(E_195, k2_struct_0('#skF_4')) | ~r2_hidden(A_193, a_2_1_orders_2('#skF_4', C_194)) | ~m1_subset_1(C_194, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_75, c_1935])).
% 4.51/1.89  tff(c_1946, plain, (![A_196, C_197, E_198]: (r2_orders_2('#skF_4', '#skF_2'(A_196, '#skF_4', C_197), E_198) | ~r2_hidden(E_198, C_197) | ~m1_subset_1(E_198, k2_struct_0('#skF_4')) | ~r2_hidden(A_196, a_2_1_orders_2('#skF_4', C_197)) | ~m1_subset_1(C_197, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_52, c_1942])).
% 4.51/1.89  tff(c_1995, plain, (![A_200, E_201]: (r2_orders_2('#skF_4', '#skF_2'(A_200, '#skF_4', k2_struct_0('#skF_4')), E_201) | ~r2_hidden(E_201, k2_struct_0('#skF_4')) | ~m1_subset_1(E_201, k2_struct_0('#skF_4')) | ~r2_hidden(A_200, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_53, c_1946])).
% 4.51/1.89  tff(c_20, plain, (![A_23, C_29]: (~r2_orders_2(A_23, C_29, C_29) | ~m1_subset_1(C_29, u1_struct_0(A_23)) | ~l1_orders_2(A_23))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.51/1.89  tff(c_2003, plain, (![A_200]: (~m1_subset_1('#skF_2'(A_200, '#skF_4', k2_struct_0('#skF_4')), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~r2_hidden('#skF_2'(A_200, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(A_200, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~r2_hidden(A_200, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_1995, c_20])).
% 4.51/1.89  tff(c_2017, plain, (![A_202]: (~r2_hidden('#skF_2'(A_202, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(A_202, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~r2_hidden(A_202, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_75, c_2003])).
% 4.51/1.89  tff(c_2023, plain, (![A_202]: (~r2_hidden(A_202, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(A_202, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_6, c_2017])).
% 4.51/1.89  tff(c_2027, plain, (![A_203]: (~r2_hidden(A_203, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~m1_subset_1('#skF_2'(A_203, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_191, c_2023])).
% 4.51/1.89  tff(c_2034, plain, (![A_106]: (~r2_hidden(A_106, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_300, c_2027])).
% 4.51/1.89  tff(c_2042, plain, (![A_204]: (~r2_hidden(A_204, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_2034])).
% 4.51/1.89  tff(c_2050, plain, (a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_2042])).
% 4.51/1.89  tff(c_2057, plain, $false, inference(negUnitSimplification, [status(thm)], [c_139, c_2050])).
% 4.51/1.89  tff(c_2059, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_190])).
% 4.51/1.89  tff(c_81, plain, (![C_57, B_58, A_59]: (~v1_xboole_0(C_57) | ~m1_subset_1(B_58, k1_zfmisc_1(C_57)) | ~r2_hidden(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.51/1.89  tff(c_86, plain, (![A_62, A_63]: (~v1_xboole_0(A_62) | ~r2_hidden(A_63, A_62))), inference(resolution, [status(thm)], [c_53, c_81])).
% 4.51/1.89  tff(c_94, plain, (![A_8]: (~v1_xboole_0(A_8) | k1_xboole_0=A_8)), inference(resolution, [status(thm)], [c_10, c_86])).
% 4.51/1.89  tff(c_2063, plain, (k2_struct_0('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_2059, c_94])).
% 4.51/1.89  tff(c_2075, plain, (a_2_1_orders_2('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2063, c_139])).
% 4.51/1.89  tff(c_2058, plain, (![A_5]: (~r2_hidden(A_5, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(splitRight, [status(thm)], [c_190])).
% 4.51/1.89  tff(c_2126, plain, (![A_208]: (~r2_hidden(A_208, a_2_1_orders_2('#skF_4', k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2063, c_2058])).
% 4.51/1.89  tff(c_2134, plain, (a_2_1_orders_2('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_2126])).
% 4.51/1.89  tff(c_2139, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2075, c_2134])).
% 4.51/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.51/1.89  
% 4.51/1.89  Inference rules
% 4.51/1.89  ----------------------
% 4.51/1.89  #Ref     : 0
% 4.51/1.89  #Sup     : 437
% 4.51/1.90  #Fact    : 0
% 4.51/1.90  #Define  : 0
% 4.51/1.90  #Split   : 4
% 4.51/1.90  #Chain   : 0
% 4.51/1.90  #Close   : 0
% 4.51/1.90  
% 4.51/1.90  Ordering : KBO
% 4.51/1.90  
% 4.51/1.90  Simplification rules
% 4.51/1.90  ----------------------
% 4.51/1.90  #Subsume      : 81
% 4.51/1.90  #Demod        : 1217
% 4.51/1.90  #Tautology    : 114
% 4.51/1.90  #SimpNegUnit  : 144
% 4.51/1.90  #BackRed      : 37
% 4.51/1.90  
% 4.51/1.90  #Partial instantiations: 0
% 4.51/1.90  #Strategies tried      : 1
% 4.51/1.90  
% 4.51/1.90  Timing (in seconds)
% 4.51/1.90  ----------------------
% 4.51/1.90  Preprocessing        : 0.34
% 4.51/1.90  Parsing              : 0.19
% 4.51/1.90  CNF conversion       : 0.02
% 4.51/1.90  Main loop            : 0.72
% 4.51/1.90  Inferencing          : 0.22
% 4.51/1.90  Reduction            : 0.27
% 4.51/1.90  Demodulation         : 0.20
% 4.51/1.90  BG Simplification    : 0.03
% 4.51/1.90  Subsumption          : 0.16
% 4.51/1.90  Abstraction          : 0.04
% 4.51/1.90  MUC search           : 0.00
% 4.51/1.90  Cooper               : 0.00
% 4.51/1.90  Total                : 1.10
% 4.51/1.90  Index Insertion      : 0.00
% 4.51/1.90  Index Deletion       : 0.00
% 4.51/1.90  Index Matching       : 0.00
% 4.51/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
