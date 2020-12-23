%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:29 EST 2020

% Result     : Theorem 3.77s
% Output     : CNFRefutation 3.77s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 492 expanded)
%              Number of leaves         :   37 ( 197 expanded)
%              Depth                    :   17
%              Number of atoms          :  210 (1306 expanded)
%              Number of equality atoms :   24 ( 244 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3

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

tff(f_35,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_37,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_145,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => k2_orders_2(A,k2_struct_0(A)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_orders_2)).

tff(f_104,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_85,axiom,(
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

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_131,axiom,(
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

tff(f_100,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_orders_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_orders_2)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_69,axiom,(
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

tff(c_4,plain,(
    ! [A_3] : k2_subset_1(A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_4] : m1_subset_1(k2_subset_1(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_49,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_46,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_44,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_42,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_40,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_24,plain,(
    ! [A_23] :
      ( l1_struct_0(A_23)
      | ~ l1_orders_2(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_61,plain,(
    ! [A_40] :
      ( u1_struct_0(A_40) = k2_struct_0(A_40)
      | ~ l1_struct_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_67,plain,(
    ! [A_42] :
      ( u1_struct_0(A_42) = k2_struct_0(A_42)
      | ~ l1_orders_2(A_42) ) ),
    inference(resolution,[status(thm)],[c_24,c_61])).

tff(c_71,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_67])).

tff(c_99,plain,(
    ! [A_61,B_62] :
      ( k2_orders_2(A_61,B_62) = a_2_1_orders_2(A_61,B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_orders_2(A_61)
      | ~ v5_orders_2(A_61)
      | ~ v4_orders_2(A_61)
      | ~ v3_orders_2(A_61)
      | v2_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_102,plain,(
    ! [B_62] :
      ( k2_orders_2('#skF_4',B_62) = a_2_1_orders_2('#skF_4',B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_99])).

tff(c_108,plain,(
    ! [B_62] :
      ( k2_orders_2('#skF_4',B_62) = a_2_1_orders_2('#skF_4',B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_102])).

tff(c_111,plain,(
    ! [B_63] :
      ( k2_orders_2('#skF_4',B_63) = a_2_1_orders_2('#skF_4',B_63)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_108])).

tff(c_116,plain,(
    k2_orders_2('#skF_4',k2_struct_0('#skF_4')) = a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_49,c_111])).

tff(c_38,plain,(
    k2_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_117,plain,(
    a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_38])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_353,plain,(
    ! [A_77,B_78,C_79] :
      ( m1_subset_1('#skF_2'(A_77,B_78,C_79),u1_struct_0(B_78))
      | ~ r2_hidden(A_77,a_2_1_orders_2(B_78,C_79))
      | ~ m1_subset_1(C_79,k1_zfmisc_1(u1_struct_0(B_78)))
      | ~ l1_orders_2(B_78)
      | ~ v5_orders_2(B_78)
      | ~ v4_orders_2(B_78)
      | ~ v3_orders_2(B_78)
      | v2_struct_0(B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_358,plain,(
    ! [A_77,C_79] :
      ( m1_subset_1('#skF_2'(A_77,'#skF_4',C_79),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_77,a_2_1_orders_2('#skF_4',C_79))
      | ~ m1_subset_1(C_79,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_353])).

tff(c_361,plain,(
    ! [A_77,C_79] :
      ( m1_subset_1('#skF_2'(A_77,'#skF_4',C_79),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_77,a_2_1_orders_2('#skF_4',C_79))
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_71,c_358])).

tff(c_362,plain,(
    ! [A_77,C_79] :
      ( m1_subset_1('#skF_2'(A_77,'#skF_4',C_79),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_77,a_2_1_orders_2('#skF_4',C_79))
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_361])).

tff(c_122,plain,(
    ! [A_64,B_65] :
      ( m1_subset_1(k2_orders_2(A_64,B_65),k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_orders_2(A_64)
      | ~ v5_orders_2(A_64)
      | ~ v4_orders_2(A_64)
      | ~ v3_orders_2(A_64)
      | v2_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_130,plain,
    ( m1_subset_1(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_122])).

tff(c_137,plain,
    ( m1_subset_1(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_49,c_71,c_71,c_130])).

tff(c_138,plain,(
    m1_subset_1(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_137])).

tff(c_10,plain,(
    ! [C_9,B_8,A_7] :
      ( ~ v1_xboole_0(C_9)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(C_9))
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_148,plain,(
    ! [A_7] :
      ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_7,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_138,c_10])).

tff(c_149,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_148])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r2_hidden(A_5,B_6)
      | v1_xboole_0(B_6)
      | ~ m1_subset_1(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1197,plain,(
    ! [B_121,A_122,C_123,E_124] :
      ( r2_orders_2(B_121,'#skF_2'(A_122,B_121,C_123),E_124)
      | ~ r2_hidden(E_124,C_123)
      | ~ m1_subset_1(E_124,u1_struct_0(B_121))
      | ~ r2_hidden(A_122,a_2_1_orders_2(B_121,C_123))
      | ~ m1_subset_1(C_123,k1_zfmisc_1(u1_struct_0(B_121)))
      | ~ l1_orders_2(B_121)
      | ~ v5_orders_2(B_121)
      | ~ v4_orders_2(B_121)
      | ~ v3_orders_2(B_121)
      | v2_struct_0(B_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1203,plain,(
    ! [A_122,C_123,E_124] :
      ( r2_orders_2('#skF_4','#skF_2'(A_122,'#skF_4',C_123),E_124)
      | ~ r2_hidden(E_124,C_123)
      | ~ m1_subset_1(E_124,u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_122,a_2_1_orders_2('#skF_4',C_123))
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_1197])).

tff(c_1210,plain,(
    ! [A_122,C_123,E_124] :
      ( r2_orders_2('#skF_4','#skF_2'(A_122,'#skF_4',C_123),E_124)
      | ~ r2_hidden(E_124,C_123)
      | ~ m1_subset_1(E_124,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_122,a_2_1_orders_2('#skF_4',C_123))
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_71,c_1203])).

tff(c_1213,plain,(
    ! [A_125,C_126,E_127] :
      ( r2_orders_2('#skF_4','#skF_2'(A_125,'#skF_4',C_126),E_127)
      | ~ r2_hidden(E_127,C_126)
      | ~ m1_subset_1(E_127,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_125,a_2_1_orders_2('#skF_4',C_126))
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1210])).

tff(c_1242,plain,(
    ! [A_128,E_129] :
      ( r2_orders_2('#skF_4','#skF_2'(A_128,'#skF_4',k2_struct_0('#skF_4')),E_129)
      | ~ r2_hidden(E_129,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_129,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_128,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_49,c_1213])).

tff(c_16,plain,(
    ! [A_11,C_17] :
      ( ~ r2_orders_2(A_11,C_17,C_17)
      | ~ m1_subset_1(C_17,u1_struct_0(A_11))
      | ~ l1_orders_2(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1250,plain,(
    ! [A_128] :
      ( ~ m1_subset_1('#skF_2'(A_128,'#skF_4',k2_struct_0('#skF_4')),u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ r2_hidden('#skF_2'(A_128,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_128,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_128,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_1242,c_16])).

tff(c_1264,plain,(
    ! [A_130] :
      ( ~ r2_hidden('#skF_2'(A_130,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_130,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_130,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_71,c_1250])).

tff(c_1270,plain,(
    ! [A_130] :
      ( ~ r2_hidden(A_130,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_130,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_8,c_1264])).

tff(c_1304,plain,(
    ! [A_131] :
      ( ~ r2_hidden(A_131,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_2'(A_131,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_1270])).

tff(c_1311,plain,(
    ! [A_77] :
      ( ~ r2_hidden(A_77,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_362,c_1304])).

tff(c_1317,plain,(
    ! [A_132] : ~ r2_hidden(A_132,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_1311])).

tff(c_1325,plain,(
    a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_1317])).

tff(c_1332,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_1325])).

tff(c_1334,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_77,plain,(
    ! [C_45,B_46,A_47] :
      ( ~ v1_xboole_0(C_45)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(C_45))
      | ~ r2_hidden(A_47,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_82,plain,(
    ! [A_50,A_51] :
      ( ~ v1_xboole_0(A_50)
      | ~ r2_hidden(A_51,A_50) ) ),
    inference(resolution,[status(thm)],[c_49,c_77])).

tff(c_90,plain,(
    ! [A_1] :
      ( ~ v1_xboole_0(A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(resolution,[status(thm)],[c_2,c_82])).

tff(c_1338,plain,(
    k2_struct_0('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1334,c_90])).

tff(c_1341,plain,(
    a_2_1_orders_2('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1338,c_117])).

tff(c_1333,plain,(
    ! [A_7] : ~ r2_hidden(A_7,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_1385,plain,(
    ! [A_136] : ~ r2_hidden(A_136,a_2_1_orders_2('#skF_4',k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1338,c_1333])).

tff(c_1393,plain,(
    a_2_1_orders_2('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_1385])).

tff(c_1398,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1341,c_1393])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.20/0.34  % DateTime   : Tue Dec  1 19:44:05 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.77/1.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.77/1.68  
% 3.77/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.77/1.68  %$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3
% 3.77/1.68  
% 3.77/1.68  %Foreground sorts:
% 3.77/1.68  
% 3.77/1.68  
% 3.77/1.68  %Background operators:
% 3.77/1.68  
% 3.77/1.68  
% 3.77/1.68  %Foreground operators:
% 3.77/1.68  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.77/1.68  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.77/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.77/1.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.77/1.68  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.77/1.68  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.77/1.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.77/1.68  tff(a_2_1_orders_2, type, a_2_1_orders_2: ($i * $i) > $i).
% 3.77/1.68  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 3.77/1.68  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.77/1.68  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.77/1.68  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.77/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.77/1.68  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.77/1.68  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.77/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.77/1.68  tff('#skF_4', type, '#skF_4': $i).
% 3.77/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.77/1.68  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 3.77/1.68  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.77/1.68  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.77/1.68  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.77/1.68  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.77/1.68  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.77/1.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.77/1.68  
% 3.77/1.70  tff(f_35, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.77/1.70  tff(f_37, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.77/1.70  tff(f_145, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k2_orders_2(A, k2_struct_0(A)) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_orders_2)).
% 3.77/1.70  tff(f_104, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 3.77/1.70  tff(f_54, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.77/1.70  tff(f_85, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_orders_2(A, B) = a_2_1_orders_2(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_orders_2)).
% 3.77/1.70  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.77/1.70  tff(f_131, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_1_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, D, E))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_1_orders_2)).
% 3.77/1.70  tff(f_100, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_orders_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_orders_2)).
% 3.77/1.70  tff(f_50, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.77/1.70  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.77/1.70  tff(f_69, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_orders_2)).
% 3.77/1.70  tff(c_4, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.77/1.70  tff(c_6, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.77/1.70  tff(c_49, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 3.77/1.70  tff(c_48, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.77/1.70  tff(c_46, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.77/1.70  tff(c_44, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.77/1.70  tff(c_42, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.77/1.70  tff(c_40, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.77/1.70  tff(c_24, plain, (![A_23]: (l1_struct_0(A_23) | ~l1_orders_2(A_23))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.77/1.70  tff(c_61, plain, (![A_40]: (u1_struct_0(A_40)=k2_struct_0(A_40) | ~l1_struct_0(A_40))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.77/1.70  tff(c_67, plain, (![A_42]: (u1_struct_0(A_42)=k2_struct_0(A_42) | ~l1_orders_2(A_42))), inference(resolution, [status(thm)], [c_24, c_61])).
% 3.77/1.70  tff(c_71, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_40, c_67])).
% 3.77/1.70  tff(c_99, plain, (![A_61, B_62]: (k2_orders_2(A_61, B_62)=a_2_1_orders_2(A_61, B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_orders_2(A_61) | ~v5_orders_2(A_61) | ~v4_orders_2(A_61) | ~v3_orders_2(A_61) | v2_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.77/1.70  tff(c_102, plain, (![B_62]: (k2_orders_2('#skF_4', B_62)=a_2_1_orders_2('#skF_4', B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_71, c_99])).
% 3.77/1.70  tff(c_108, plain, (![B_62]: (k2_orders_2('#skF_4', B_62)=a_2_1_orders_2('#skF_4', B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_102])).
% 3.77/1.70  tff(c_111, plain, (![B_63]: (k2_orders_2('#skF_4', B_63)=a_2_1_orders_2('#skF_4', B_63) | ~m1_subset_1(B_63, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_48, c_108])).
% 3.77/1.70  tff(c_116, plain, (k2_orders_2('#skF_4', k2_struct_0('#skF_4'))=a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_49, c_111])).
% 3.77/1.70  tff(c_38, plain, (k2_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.77/1.70  tff(c_117, plain, (a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_116, c_38])).
% 3.77/1.70  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.77/1.70  tff(c_353, plain, (![A_77, B_78, C_79]: (m1_subset_1('#skF_2'(A_77, B_78, C_79), u1_struct_0(B_78)) | ~r2_hidden(A_77, a_2_1_orders_2(B_78, C_79)) | ~m1_subset_1(C_79, k1_zfmisc_1(u1_struct_0(B_78))) | ~l1_orders_2(B_78) | ~v5_orders_2(B_78) | ~v4_orders_2(B_78) | ~v3_orders_2(B_78) | v2_struct_0(B_78))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.77/1.70  tff(c_358, plain, (![A_77, C_79]: (m1_subset_1('#skF_2'(A_77, '#skF_4', C_79), k2_struct_0('#skF_4')) | ~r2_hidden(A_77, a_2_1_orders_2('#skF_4', C_79)) | ~m1_subset_1(C_79, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_71, c_353])).
% 3.77/1.70  tff(c_361, plain, (![A_77, C_79]: (m1_subset_1('#skF_2'(A_77, '#skF_4', C_79), k2_struct_0('#skF_4')) | ~r2_hidden(A_77, a_2_1_orders_2('#skF_4', C_79)) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_71, c_358])).
% 3.77/1.70  tff(c_362, plain, (![A_77, C_79]: (m1_subset_1('#skF_2'(A_77, '#skF_4', C_79), k2_struct_0('#skF_4')) | ~r2_hidden(A_77, a_2_1_orders_2('#skF_4', C_79)) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_48, c_361])).
% 3.77/1.70  tff(c_122, plain, (![A_64, B_65]: (m1_subset_1(k2_orders_2(A_64, B_65), k1_zfmisc_1(u1_struct_0(A_64))) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_orders_2(A_64) | ~v5_orders_2(A_64) | ~v4_orders_2(A_64) | ~v3_orders_2(A_64) | v2_struct_0(A_64))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.77/1.70  tff(c_130, plain, (m1_subset_1(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_116, c_122])).
% 3.77/1.70  tff(c_137, plain, (m1_subset_1(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')), k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_49, c_71, c_71, c_130])).
% 3.77/1.70  tff(c_138, plain, (m1_subset_1(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_48, c_137])).
% 3.77/1.70  tff(c_10, plain, (![C_9, B_8, A_7]: (~v1_xboole_0(C_9) | ~m1_subset_1(B_8, k1_zfmisc_1(C_9)) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.77/1.70  tff(c_148, plain, (![A_7]: (~v1_xboole_0(k2_struct_0('#skF_4')) | ~r2_hidden(A_7, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_138, c_10])).
% 3.77/1.70  tff(c_149, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_148])).
% 3.77/1.70  tff(c_8, plain, (![A_5, B_6]: (r2_hidden(A_5, B_6) | v1_xboole_0(B_6) | ~m1_subset_1(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.77/1.70  tff(c_1197, plain, (![B_121, A_122, C_123, E_124]: (r2_orders_2(B_121, '#skF_2'(A_122, B_121, C_123), E_124) | ~r2_hidden(E_124, C_123) | ~m1_subset_1(E_124, u1_struct_0(B_121)) | ~r2_hidden(A_122, a_2_1_orders_2(B_121, C_123)) | ~m1_subset_1(C_123, k1_zfmisc_1(u1_struct_0(B_121))) | ~l1_orders_2(B_121) | ~v5_orders_2(B_121) | ~v4_orders_2(B_121) | ~v3_orders_2(B_121) | v2_struct_0(B_121))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.77/1.70  tff(c_1203, plain, (![A_122, C_123, E_124]: (r2_orders_2('#skF_4', '#skF_2'(A_122, '#skF_4', C_123), E_124) | ~r2_hidden(E_124, C_123) | ~m1_subset_1(E_124, u1_struct_0('#skF_4')) | ~r2_hidden(A_122, a_2_1_orders_2('#skF_4', C_123)) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_71, c_1197])).
% 3.77/1.70  tff(c_1210, plain, (![A_122, C_123, E_124]: (r2_orders_2('#skF_4', '#skF_2'(A_122, '#skF_4', C_123), E_124) | ~r2_hidden(E_124, C_123) | ~m1_subset_1(E_124, k2_struct_0('#skF_4')) | ~r2_hidden(A_122, a_2_1_orders_2('#skF_4', C_123)) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_71, c_1203])).
% 3.77/1.70  tff(c_1213, plain, (![A_125, C_126, E_127]: (r2_orders_2('#skF_4', '#skF_2'(A_125, '#skF_4', C_126), E_127) | ~r2_hidden(E_127, C_126) | ~m1_subset_1(E_127, k2_struct_0('#skF_4')) | ~r2_hidden(A_125, a_2_1_orders_2('#skF_4', C_126)) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_48, c_1210])).
% 3.77/1.70  tff(c_1242, plain, (![A_128, E_129]: (r2_orders_2('#skF_4', '#skF_2'(A_128, '#skF_4', k2_struct_0('#skF_4')), E_129) | ~r2_hidden(E_129, k2_struct_0('#skF_4')) | ~m1_subset_1(E_129, k2_struct_0('#skF_4')) | ~r2_hidden(A_128, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_49, c_1213])).
% 3.77/1.70  tff(c_16, plain, (![A_11, C_17]: (~r2_orders_2(A_11, C_17, C_17) | ~m1_subset_1(C_17, u1_struct_0(A_11)) | ~l1_orders_2(A_11))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.77/1.70  tff(c_1250, plain, (![A_128]: (~m1_subset_1('#skF_2'(A_128, '#skF_4', k2_struct_0('#skF_4')), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~r2_hidden('#skF_2'(A_128, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(A_128, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~r2_hidden(A_128, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_1242, c_16])).
% 3.77/1.70  tff(c_1264, plain, (![A_130]: (~r2_hidden('#skF_2'(A_130, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(A_130, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~r2_hidden(A_130, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_71, c_1250])).
% 3.77/1.70  tff(c_1270, plain, (![A_130]: (~r2_hidden(A_130, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(A_130, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_8, c_1264])).
% 3.77/1.70  tff(c_1304, plain, (![A_131]: (~r2_hidden(A_131, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~m1_subset_1('#skF_2'(A_131, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_149, c_1270])).
% 3.77/1.70  tff(c_1311, plain, (![A_77]: (~r2_hidden(A_77, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_362, c_1304])).
% 3.77/1.70  tff(c_1317, plain, (![A_132]: (~r2_hidden(A_132, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_1311])).
% 3.77/1.70  tff(c_1325, plain, (a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_1317])).
% 3.77/1.70  tff(c_1332, plain, $false, inference(negUnitSimplification, [status(thm)], [c_117, c_1325])).
% 3.77/1.70  tff(c_1334, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_148])).
% 3.77/1.70  tff(c_77, plain, (![C_45, B_46, A_47]: (~v1_xboole_0(C_45) | ~m1_subset_1(B_46, k1_zfmisc_1(C_45)) | ~r2_hidden(A_47, B_46))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.77/1.70  tff(c_82, plain, (![A_50, A_51]: (~v1_xboole_0(A_50) | ~r2_hidden(A_51, A_50))), inference(resolution, [status(thm)], [c_49, c_77])).
% 3.77/1.70  tff(c_90, plain, (![A_1]: (~v1_xboole_0(A_1) | k1_xboole_0=A_1)), inference(resolution, [status(thm)], [c_2, c_82])).
% 3.77/1.70  tff(c_1338, plain, (k2_struct_0('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_1334, c_90])).
% 3.77/1.70  tff(c_1341, plain, (a_2_1_orders_2('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1338, c_117])).
% 3.77/1.70  tff(c_1333, plain, (![A_7]: (~r2_hidden(A_7, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(splitRight, [status(thm)], [c_148])).
% 3.77/1.70  tff(c_1385, plain, (![A_136]: (~r2_hidden(A_136, a_2_1_orders_2('#skF_4', k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_1338, c_1333])).
% 3.77/1.70  tff(c_1393, plain, (a_2_1_orders_2('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_1385])).
% 3.77/1.70  tff(c_1398, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1341, c_1393])).
% 3.77/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.77/1.70  
% 3.77/1.70  Inference rules
% 3.77/1.70  ----------------------
% 3.77/1.70  #Ref     : 0
% 3.77/1.70  #Sup     : 289
% 3.77/1.70  #Fact    : 0
% 3.77/1.70  #Define  : 0
% 3.77/1.70  #Split   : 2
% 3.77/1.70  #Chain   : 0
% 3.77/1.70  #Close   : 0
% 3.77/1.70  
% 3.77/1.70  Ordering : KBO
% 3.77/1.70  
% 3.77/1.70  Simplification rules
% 3.77/1.70  ----------------------
% 3.77/1.70  #Subsume      : 53
% 3.77/1.70  #Demod        : 840
% 3.77/1.70  #Tautology    : 81
% 3.77/1.70  #SimpNegUnit  : 85
% 3.77/1.70  #BackRed      : 10
% 3.77/1.70  
% 3.77/1.70  #Partial instantiations: 0
% 3.77/1.70  #Strategies tried      : 1
% 3.77/1.70  
% 3.77/1.70  Timing (in seconds)
% 3.77/1.70  ----------------------
% 3.77/1.70  Preprocessing        : 0.33
% 3.77/1.70  Parsing              : 0.17
% 3.77/1.70  CNF conversion       : 0.02
% 3.77/1.70  Main loop            : 0.56
% 3.77/1.70  Inferencing          : 0.18
% 3.77/1.70  Reduction            : 0.19
% 3.77/1.70  Demodulation         : 0.14
% 3.77/1.70  BG Simplification    : 0.03
% 3.77/1.70  Subsumption          : 0.14
% 3.77/1.70  Abstraction          : 0.03
% 3.77/1.70  MUC search           : 0.00
% 3.77/1.70  Cooper               : 0.00
% 3.77/1.70  Total                : 0.93
% 3.77/1.70  Index Insertion      : 0.00
% 3.77/1.70  Index Deletion       : 0.00
% 3.77/1.70  Index Matching       : 0.00
% 3.77/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
