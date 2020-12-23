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
% DateTime   : Thu Dec  3 10:19:26 EST 2020

% Result     : Theorem 4.06s
% Output     : CNFRefutation 4.37s
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
%$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_37,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_145,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => k1_orders_2(A,k2_struct_0(A)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_orders_2)).

tff(f_104,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_85,axiom,(
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

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_131,axiom,(
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

tff(f_100,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_orders_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_orders_2)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).

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
      ( k1_orders_2(A_61,B_62) = a_2_0_orders_2(A_61,B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_orders_2(A_61)
      | ~ v5_orders_2(A_61)
      | ~ v4_orders_2(A_61)
      | ~ v3_orders_2(A_61)
      | v2_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_102,plain,(
    ! [B_62] :
      ( k1_orders_2('#skF_4',B_62) = a_2_0_orders_2('#skF_4',B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_99])).

tff(c_108,plain,(
    ! [B_62] :
      ( k1_orders_2('#skF_4',B_62) = a_2_0_orders_2('#skF_4',B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_102])).

tff(c_111,plain,(
    ! [B_63] :
      ( k1_orders_2('#skF_4',B_63) = a_2_0_orders_2('#skF_4',B_63)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_108])).

tff(c_116,plain,(
    k1_orders_2('#skF_4',k2_struct_0('#skF_4')) = a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_49,c_111])).

tff(c_38,plain,(
    k1_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_117,plain,(
    a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_38])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_353,plain,(
    ! [A_77,B_78,C_79] :
      ( m1_subset_1('#skF_2'(A_77,B_78,C_79),u1_struct_0(B_78))
      | ~ r2_hidden(A_77,a_2_0_orders_2(B_78,C_79))
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
      | ~ r2_hidden(A_77,a_2_0_orders_2('#skF_4',C_79))
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
      | ~ r2_hidden(A_77,a_2_0_orders_2('#skF_4',C_79))
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_71,c_358])).

tff(c_362,plain,(
    ! [A_77,C_79] :
      ( m1_subset_1('#skF_2'(A_77,'#skF_4',C_79),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_77,a_2_0_orders_2('#skF_4',C_79))
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_361])).

tff(c_122,plain,(
    ! [A_64,B_65] :
      ( m1_subset_1(k1_orders_2(A_64,B_65),k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_orders_2(A_64)
      | ~ v5_orders_2(A_64)
      | ~ v4_orders_2(A_64)
      | ~ v3_orders_2(A_64)
      | v2_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_130,plain,
    ( m1_subset_1(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_122])).

tff(c_137,plain,
    ( m1_subset_1(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_49,c_71,c_71,c_130])).

tff(c_138,plain,(
    m1_subset_1(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
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
      | ~ r2_hidden(A_7,a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
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
    ! [B_121,E_122,A_123,C_124] :
      ( r2_orders_2(B_121,E_122,'#skF_2'(A_123,B_121,C_124))
      | ~ r2_hidden(E_122,C_124)
      | ~ m1_subset_1(E_122,u1_struct_0(B_121))
      | ~ r2_hidden(A_123,a_2_0_orders_2(B_121,C_124))
      | ~ m1_subset_1(C_124,k1_zfmisc_1(u1_struct_0(B_121)))
      | ~ l1_orders_2(B_121)
      | ~ v5_orders_2(B_121)
      | ~ v4_orders_2(B_121)
      | ~ v3_orders_2(B_121)
      | v2_struct_0(B_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1203,plain,(
    ! [E_122,A_123,C_124] :
      ( r2_orders_2('#skF_4',E_122,'#skF_2'(A_123,'#skF_4',C_124))
      | ~ r2_hidden(E_122,C_124)
      | ~ m1_subset_1(E_122,u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_123,a_2_0_orders_2('#skF_4',C_124))
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_1197])).

tff(c_1210,plain,(
    ! [E_122,A_123,C_124] :
      ( r2_orders_2('#skF_4',E_122,'#skF_2'(A_123,'#skF_4',C_124))
      | ~ r2_hidden(E_122,C_124)
      | ~ m1_subset_1(E_122,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_123,a_2_0_orders_2('#skF_4',C_124))
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_71,c_1203])).

tff(c_1213,plain,(
    ! [E_125,A_126,C_127] :
      ( r2_orders_2('#skF_4',E_125,'#skF_2'(A_126,'#skF_4',C_127))
      | ~ r2_hidden(E_125,C_127)
      | ~ m1_subset_1(E_125,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_126,a_2_0_orders_2('#skF_4',C_127))
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1210])).

tff(c_1242,plain,(
    ! [E_128,A_129] :
      ( r2_orders_2('#skF_4',E_128,'#skF_2'(A_129,'#skF_4',k2_struct_0('#skF_4')))
      | ~ r2_hidden(E_128,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_128,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_129,a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_49,c_1213])).

tff(c_16,plain,(
    ! [A_11,C_17] :
      ( ~ r2_orders_2(A_11,C_17,C_17)
      | ~ m1_subset_1(C_17,u1_struct_0(A_11))
      | ~ l1_orders_2(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1250,plain,(
    ! [A_129] :
      ( ~ m1_subset_1('#skF_2'(A_129,'#skF_4',k2_struct_0('#skF_4')),u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ r2_hidden('#skF_2'(A_129,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_129,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_129,a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_1242,c_16])).

tff(c_1264,plain,(
    ! [A_130] :
      ( ~ r2_hidden('#skF_2'(A_130,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_130,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_130,a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_71,c_1250])).

tff(c_1270,plain,(
    ! [A_130] :
      ( ~ r2_hidden(A_130,a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_130,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_8,c_1264])).

tff(c_1304,plain,(
    ! [A_131] :
      ( ~ r2_hidden(A_131,a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_2'(A_131,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_1270])).

tff(c_1311,plain,(
    ! [A_77] :
      ( ~ r2_hidden(A_77,a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_362,c_1304])).

tff(c_1317,plain,(
    ! [A_132] : ~ r2_hidden(A_132,a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_1311])).

tff(c_1325,plain,(
    a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ),
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
    a_2_0_orders_2('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1338,c_117])).

tff(c_1333,plain,(
    ! [A_7] : ~ r2_hidden(A_7,a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_1385,plain,(
    ! [A_136] : ~ r2_hidden(A_136,a_2_0_orders_2('#skF_4',k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1338,c_1333])).

tff(c_1393,plain,(
    a_2_0_orders_2('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_1385])).

tff(c_1398,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1341,c_1393])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:29:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.06/1.73  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.06/1.74  
% 4.06/1.74  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.06/1.74  %$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3
% 4.06/1.74  
% 4.06/1.74  %Foreground sorts:
% 4.06/1.74  
% 4.06/1.74  
% 4.06/1.74  %Background operators:
% 4.06/1.74  
% 4.06/1.74  
% 4.06/1.74  %Foreground operators:
% 4.06/1.74  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.06/1.74  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 4.06/1.74  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 4.06/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.06/1.74  tff(a_2_0_orders_2, type, a_2_0_orders_2: ($i * $i) > $i).
% 4.06/1.74  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.06/1.74  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.06/1.74  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 4.06/1.74  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.06/1.74  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.06/1.74  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 4.06/1.74  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 4.06/1.74  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.06/1.74  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.06/1.74  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 4.06/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.06/1.74  tff('#skF_4', type, '#skF_4': $i).
% 4.06/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.06/1.74  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 4.06/1.74  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 4.06/1.74  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.06/1.74  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.06/1.74  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.06/1.74  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.06/1.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.06/1.74  
% 4.37/1.76  tff(f_35, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 4.37/1.76  tff(f_37, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.37/1.76  tff(f_145, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k1_orders_2(A, k2_struct_0(A)) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_orders_2)).
% 4.37/1.76  tff(f_104, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 4.37/1.76  tff(f_54, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 4.37/1.76  tff(f_85, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_orders_2(A, B) = a_2_0_orders_2(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_orders_2)).
% 4.37/1.76  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.37/1.76  tff(f_131, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_0_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, E, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_0_orders_2)).
% 4.37/1.76  tff(f_100, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_orders_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_orders_2)).
% 4.37/1.76  tff(f_50, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 4.37/1.76  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 4.37/1.76  tff(f_69, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_orders_2)).
% 4.37/1.76  tff(c_4, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.37/1.76  tff(c_6, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.37/1.76  tff(c_49, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 4.37/1.76  tff(c_48, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.37/1.76  tff(c_46, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.37/1.76  tff(c_44, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.37/1.76  tff(c_42, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.37/1.76  tff(c_40, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.37/1.76  tff(c_24, plain, (![A_23]: (l1_struct_0(A_23) | ~l1_orders_2(A_23))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.37/1.76  tff(c_61, plain, (![A_40]: (u1_struct_0(A_40)=k2_struct_0(A_40) | ~l1_struct_0(A_40))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.37/1.76  tff(c_67, plain, (![A_42]: (u1_struct_0(A_42)=k2_struct_0(A_42) | ~l1_orders_2(A_42))), inference(resolution, [status(thm)], [c_24, c_61])).
% 4.37/1.76  tff(c_71, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_40, c_67])).
% 4.37/1.76  tff(c_99, plain, (![A_61, B_62]: (k1_orders_2(A_61, B_62)=a_2_0_orders_2(A_61, B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_orders_2(A_61) | ~v5_orders_2(A_61) | ~v4_orders_2(A_61) | ~v3_orders_2(A_61) | v2_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.37/1.76  tff(c_102, plain, (![B_62]: (k1_orders_2('#skF_4', B_62)=a_2_0_orders_2('#skF_4', B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_71, c_99])).
% 4.37/1.76  tff(c_108, plain, (![B_62]: (k1_orders_2('#skF_4', B_62)=a_2_0_orders_2('#skF_4', B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_102])).
% 4.37/1.76  tff(c_111, plain, (![B_63]: (k1_orders_2('#skF_4', B_63)=a_2_0_orders_2('#skF_4', B_63) | ~m1_subset_1(B_63, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_48, c_108])).
% 4.37/1.76  tff(c_116, plain, (k1_orders_2('#skF_4', k2_struct_0('#skF_4'))=a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_49, c_111])).
% 4.37/1.76  tff(c_38, plain, (k1_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.37/1.76  tff(c_117, plain, (a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_116, c_38])).
% 4.37/1.76  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.37/1.76  tff(c_353, plain, (![A_77, B_78, C_79]: (m1_subset_1('#skF_2'(A_77, B_78, C_79), u1_struct_0(B_78)) | ~r2_hidden(A_77, a_2_0_orders_2(B_78, C_79)) | ~m1_subset_1(C_79, k1_zfmisc_1(u1_struct_0(B_78))) | ~l1_orders_2(B_78) | ~v5_orders_2(B_78) | ~v4_orders_2(B_78) | ~v3_orders_2(B_78) | v2_struct_0(B_78))), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.37/1.76  tff(c_358, plain, (![A_77, C_79]: (m1_subset_1('#skF_2'(A_77, '#skF_4', C_79), k2_struct_0('#skF_4')) | ~r2_hidden(A_77, a_2_0_orders_2('#skF_4', C_79)) | ~m1_subset_1(C_79, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_71, c_353])).
% 4.37/1.76  tff(c_361, plain, (![A_77, C_79]: (m1_subset_1('#skF_2'(A_77, '#skF_4', C_79), k2_struct_0('#skF_4')) | ~r2_hidden(A_77, a_2_0_orders_2('#skF_4', C_79)) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_71, c_358])).
% 4.37/1.76  tff(c_362, plain, (![A_77, C_79]: (m1_subset_1('#skF_2'(A_77, '#skF_4', C_79), k2_struct_0('#skF_4')) | ~r2_hidden(A_77, a_2_0_orders_2('#skF_4', C_79)) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_48, c_361])).
% 4.37/1.76  tff(c_122, plain, (![A_64, B_65]: (m1_subset_1(k1_orders_2(A_64, B_65), k1_zfmisc_1(u1_struct_0(A_64))) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_orders_2(A_64) | ~v5_orders_2(A_64) | ~v4_orders_2(A_64) | ~v3_orders_2(A_64) | v2_struct_0(A_64))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.37/1.76  tff(c_130, plain, (m1_subset_1(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_116, c_122])).
% 4.37/1.76  tff(c_137, plain, (m1_subset_1(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')), k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_49, c_71, c_71, c_130])).
% 4.37/1.76  tff(c_138, plain, (m1_subset_1(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_48, c_137])).
% 4.37/1.76  tff(c_10, plain, (![C_9, B_8, A_7]: (~v1_xboole_0(C_9) | ~m1_subset_1(B_8, k1_zfmisc_1(C_9)) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.37/1.76  tff(c_148, plain, (![A_7]: (~v1_xboole_0(k2_struct_0('#skF_4')) | ~r2_hidden(A_7, a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_138, c_10])).
% 4.37/1.76  tff(c_149, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_148])).
% 4.37/1.76  tff(c_8, plain, (![A_5, B_6]: (r2_hidden(A_5, B_6) | v1_xboole_0(B_6) | ~m1_subset_1(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.37/1.76  tff(c_1197, plain, (![B_121, E_122, A_123, C_124]: (r2_orders_2(B_121, E_122, '#skF_2'(A_123, B_121, C_124)) | ~r2_hidden(E_122, C_124) | ~m1_subset_1(E_122, u1_struct_0(B_121)) | ~r2_hidden(A_123, a_2_0_orders_2(B_121, C_124)) | ~m1_subset_1(C_124, k1_zfmisc_1(u1_struct_0(B_121))) | ~l1_orders_2(B_121) | ~v5_orders_2(B_121) | ~v4_orders_2(B_121) | ~v3_orders_2(B_121) | v2_struct_0(B_121))), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.37/1.76  tff(c_1203, plain, (![E_122, A_123, C_124]: (r2_orders_2('#skF_4', E_122, '#skF_2'(A_123, '#skF_4', C_124)) | ~r2_hidden(E_122, C_124) | ~m1_subset_1(E_122, u1_struct_0('#skF_4')) | ~r2_hidden(A_123, a_2_0_orders_2('#skF_4', C_124)) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_71, c_1197])).
% 4.37/1.76  tff(c_1210, plain, (![E_122, A_123, C_124]: (r2_orders_2('#skF_4', E_122, '#skF_2'(A_123, '#skF_4', C_124)) | ~r2_hidden(E_122, C_124) | ~m1_subset_1(E_122, k2_struct_0('#skF_4')) | ~r2_hidden(A_123, a_2_0_orders_2('#skF_4', C_124)) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_71, c_1203])).
% 4.37/1.76  tff(c_1213, plain, (![E_125, A_126, C_127]: (r2_orders_2('#skF_4', E_125, '#skF_2'(A_126, '#skF_4', C_127)) | ~r2_hidden(E_125, C_127) | ~m1_subset_1(E_125, k2_struct_0('#skF_4')) | ~r2_hidden(A_126, a_2_0_orders_2('#skF_4', C_127)) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_48, c_1210])).
% 4.37/1.76  tff(c_1242, plain, (![E_128, A_129]: (r2_orders_2('#skF_4', E_128, '#skF_2'(A_129, '#skF_4', k2_struct_0('#skF_4'))) | ~r2_hidden(E_128, k2_struct_0('#skF_4')) | ~m1_subset_1(E_128, k2_struct_0('#skF_4')) | ~r2_hidden(A_129, a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_49, c_1213])).
% 4.37/1.76  tff(c_16, plain, (![A_11, C_17]: (~r2_orders_2(A_11, C_17, C_17) | ~m1_subset_1(C_17, u1_struct_0(A_11)) | ~l1_orders_2(A_11))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.37/1.76  tff(c_1250, plain, (![A_129]: (~m1_subset_1('#skF_2'(A_129, '#skF_4', k2_struct_0('#skF_4')), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~r2_hidden('#skF_2'(A_129, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(A_129, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~r2_hidden(A_129, a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_1242, c_16])).
% 4.37/1.76  tff(c_1264, plain, (![A_130]: (~r2_hidden('#skF_2'(A_130, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(A_130, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~r2_hidden(A_130, a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_71, c_1250])).
% 4.37/1.76  tff(c_1270, plain, (![A_130]: (~r2_hidden(A_130, a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(A_130, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_8, c_1264])).
% 4.37/1.76  tff(c_1304, plain, (![A_131]: (~r2_hidden(A_131, a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~m1_subset_1('#skF_2'(A_131, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_149, c_1270])).
% 4.37/1.76  tff(c_1311, plain, (![A_77]: (~r2_hidden(A_77, a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_362, c_1304])).
% 4.37/1.76  tff(c_1317, plain, (![A_132]: (~r2_hidden(A_132, a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_1311])).
% 4.37/1.76  tff(c_1325, plain, (a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_1317])).
% 4.37/1.76  tff(c_1332, plain, $false, inference(negUnitSimplification, [status(thm)], [c_117, c_1325])).
% 4.37/1.76  tff(c_1334, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_148])).
% 4.37/1.76  tff(c_77, plain, (![C_45, B_46, A_47]: (~v1_xboole_0(C_45) | ~m1_subset_1(B_46, k1_zfmisc_1(C_45)) | ~r2_hidden(A_47, B_46))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.37/1.76  tff(c_82, plain, (![A_50, A_51]: (~v1_xboole_0(A_50) | ~r2_hidden(A_51, A_50))), inference(resolution, [status(thm)], [c_49, c_77])).
% 4.37/1.76  tff(c_90, plain, (![A_1]: (~v1_xboole_0(A_1) | k1_xboole_0=A_1)), inference(resolution, [status(thm)], [c_2, c_82])).
% 4.37/1.76  tff(c_1338, plain, (k2_struct_0('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_1334, c_90])).
% 4.37/1.76  tff(c_1341, plain, (a_2_0_orders_2('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1338, c_117])).
% 4.37/1.76  tff(c_1333, plain, (![A_7]: (~r2_hidden(A_7, a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(splitRight, [status(thm)], [c_148])).
% 4.37/1.76  tff(c_1385, plain, (![A_136]: (~r2_hidden(A_136, a_2_0_orders_2('#skF_4', k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_1338, c_1333])).
% 4.37/1.76  tff(c_1393, plain, (a_2_0_orders_2('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_1385])).
% 4.37/1.76  tff(c_1398, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1341, c_1393])).
% 4.37/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.37/1.76  
% 4.37/1.76  Inference rules
% 4.37/1.76  ----------------------
% 4.37/1.76  #Ref     : 0
% 4.37/1.76  #Sup     : 289
% 4.37/1.76  #Fact    : 0
% 4.37/1.76  #Define  : 0
% 4.37/1.76  #Split   : 2
% 4.37/1.76  #Chain   : 0
% 4.37/1.76  #Close   : 0
% 4.37/1.76  
% 4.37/1.76  Ordering : KBO
% 4.37/1.76  
% 4.37/1.76  Simplification rules
% 4.37/1.76  ----------------------
% 4.37/1.76  #Subsume      : 53
% 4.37/1.76  #Demod        : 840
% 4.37/1.76  #Tautology    : 81
% 4.37/1.76  #SimpNegUnit  : 85
% 4.37/1.76  #BackRed      : 10
% 4.37/1.76  
% 4.37/1.76  #Partial instantiations: 0
% 4.37/1.76  #Strategies tried      : 1
% 4.37/1.76  
% 4.37/1.76  Timing (in seconds)
% 4.37/1.76  ----------------------
% 4.37/1.77  Preprocessing        : 0.35
% 4.37/1.77  Parsing              : 0.18
% 4.37/1.77  CNF conversion       : 0.03
% 4.37/1.77  Main loop            : 0.62
% 4.37/1.77  Inferencing          : 0.20
% 4.37/1.77  Reduction            : 0.21
% 4.37/1.77  Demodulation         : 0.16
% 4.37/1.77  BG Simplification    : 0.03
% 4.37/1.77  Subsumption          : 0.15
% 4.37/1.77  Abstraction          : 0.03
% 4.37/1.77  MUC search           : 0.00
% 4.37/1.77  Cooper               : 0.00
% 4.37/1.77  Total                : 1.01
% 4.37/1.77  Index Insertion      : 0.00
% 4.37/1.77  Index Deletion       : 0.00
% 4.37/1.77  Index Matching       : 0.00
% 4.37/1.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
