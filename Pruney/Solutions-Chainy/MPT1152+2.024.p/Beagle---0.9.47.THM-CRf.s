%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:31 EST 2020

% Result     : Theorem 4.43s
% Output     : CNFRefutation 4.43s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 587 expanded)
%              Number of leaves         :   35 ( 210 expanded)
%              Depth                    :   20
%              Number of atoms          :  234 (1385 expanded)
%              Number of equality atoms :   28 ( 261 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_145,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => k2_orders_2(A,k2_struct_0(A)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_orders_2)).

tff(f_104,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_orders_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_39,axiom,(
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

tff(f_100,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_orders_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_orders_2)).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_38,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_22,plain,(
    ! [A_22] :
      ( l1_struct_0(A_22)
      | ~ l1_orders_2(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_49,plain,(
    ! [A_38] :
      ( u1_struct_0(A_38) = k2_struct_0(A_38)
      | ~ l1_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_55,plain,(
    ! [A_40] :
      ( u1_struct_0(A_40) = k2_struct_0(A_40)
      | ~ l1_orders_2(A_40) ) ),
    inference(resolution,[status(thm)],[c_22,c_49])).

tff(c_59,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_55])).

tff(c_10,plain,(
    ! [A_9] :
      ( m1_subset_1(k2_struct_0(A_9),k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ l1_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_63,plain,
    ( m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ l1_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_10])).

tff(c_68,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_63])).

tff(c_71,plain,(
    ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_68])).

tff(c_75,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_71])).

tff(c_76,plain,(
    m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_63])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_44,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_42,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_40,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_117,plain,(
    ! [A_61,B_62] :
      ( k2_orders_2(A_61,B_62) = a_2_1_orders_2(A_61,B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_orders_2(A_61)
      | ~ v5_orders_2(A_61)
      | ~ v4_orders_2(A_61)
      | ~ v3_orders_2(A_61)
      | v2_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_120,plain,(
    ! [B_62] :
      ( k2_orders_2('#skF_4',B_62) = a_2_1_orders_2('#skF_4',B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_117])).

tff(c_125,plain,(
    ! [B_62] :
      ( k2_orders_2('#skF_4',B_62) = a_2_1_orders_2('#skF_4',B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_120])).

tff(c_128,plain,(
    ! [B_63] :
      ( k2_orders_2('#skF_4',B_63) = a_2_1_orders_2('#skF_4',B_63)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_125])).

tff(c_132,plain,(
    k2_orders_2('#skF_4',k2_struct_0('#skF_4')) = a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_76,c_128])).

tff(c_36,plain,(
    k2_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_133,plain,(
    a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_36])).

tff(c_314,plain,(
    ! [A_73,B_74,C_75] :
      ( m1_subset_1('#skF_2'(A_73,B_74,C_75),u1_struct_0(B_74))
      | ~ r2_hidden(A_73,a_2_1_orders_2(B_74,C_75))
      | ~ m1_subset_1(C_75,k1_zfmisc_1(u1_struct_0(B_74)))
      | ~ l1_orders_2(B_74)
      | ~ v5_orders_2(B_74)
      | ~ v4_orders_2(B_74)
      | ~ v3_orders_2(B_74)
      | v2_struct_0(B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_319,plain,(
    ! [A_73,C_75] :
      ( m1_subset_1('#skF_2'(A_73,'#skF_4',C_75),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_73,a_2_1_orders_2('#skF_4',C_75))
      | ~ m1_subset_1(C_75,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_314])).

tff(c_322,plain,(
    ! [A_73,C_75] :
      ( m1_subset_1('#skF_2'(A_73,'#skF_4',C_75),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_73,a_2_1_orders_2('#skF_4',C_75))
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_59,c_319])).

tff(c_323,plain,(
    ! [A_73,C_75] :
      ( m1_subset_1('#skF_2'(A_73,'#skF_4',C_75),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_73,a_2_1_orders_2('#skF_4',C_75))
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_322])).

tff(c_6,plain,(
    ! [C_7,B_6,A_5] :
      ( ~ v1_xboole_0(C_7)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(C_7))
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_89,plain,(
    ! [A_5] :
      ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_5,k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_76,c_6])).

tff(c_90,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_89])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1293,plain,(
    ! [B_120,A_121,C_122,E_123] :
      ( r2_orders_2(B_120,'#skF_2'(A_121,B_120,C_122),E_123)
      | ~ r2_hidden(E_123,C_122)
      | ~ m1_subset_1(E_123,u1_struct_0(B_120))
      | ~ r2_hidden(A_121,a_2_1_orders_2(B_120,C_122))
      | ~ m1_subset_1(C_122,k1_zfmisc_1(u1_struct_0(B_120)))
      | ~ l1_orders_2(B_120)
      | ~ v5_orders_2(B_120)
      | ~ v4_orders_2(B_120)
      | ~ v3_orders_2(B_120)
      | v2_struct_0(B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1297,plain,(
    ! [A_121,C_122,E_123] :
      ( r2_orders_2('#skF_4','#skF_2'(A_121,'#skF_4',C_122),E_123)
      | ~ r2_hidden(E_123,C_122)
      | ~ m1_subset_1(E_123,u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_121,a_2_1_orders_2('#skF_4',C_122))
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_1293])).

tff(c_1302,plain,(
    ! [A_121,C_122,E_123] :
      ( r2_orders_2('#skF_4','#skF_2'(A_121,'#skF_4',C_122),E_123)
      | ~ r2_hidden(E_123,C_122)
      | ~ m1_subset_1(E_123,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_121,a_2_1_orders_2('#skF_4',C_122))
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_59,c_1297])).

tff(c_1305,plain,(
    ! [A_124,C_125,E_126] :
      ( r2_orders_2('#skF_4','#skF_2'(A_124,'#skF_4',C_125),E_126)
      | ~ r2_hidden(E_126,C_125)
      | ~ m1_subset_1(E_126,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_124,a_2_1_orders_2('#skF_4',C_125))
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1302])).

tff(c_1333,plain,(
    ! [A_127,E_128] :
      ( r2_orders_2('#skF_4','#skF_2'(A_127,'#skF_4',k2_struct_0('#skF_4')),E_128)
      | ~ r2_hidden(E_128,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_128,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_127,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_76,c_1305])).

tff(c_14,plain,(
    ! [A_10,C_16] :
      ( ~ r2_orders_2(A_10,C_16,C_16)
      | ~ m1_subset_1(C_16,u1_struct_0(A_10))
      | ~ l1_orders_2(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1341,plain,(
    ! [A_127] :
      ( ~ m1_subset_1('#skF_2'(A_127,'#skF_4',k2_struct_0('#skF_4')),u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ r2_hidden('#skF_2'(A_127,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_127,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_127,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_1333,c_14])).

tff(c_1352,plain,(
    ! [A_129] :
      ( ~ r2_hidden('#skF_2'(A_129,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_129,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_129,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_59,c_1341])).

tff(c_1355,plain,(
    ! [A_129] :
      ( ~ r2_hidden(A_129,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_129,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_4,c_1352])).

tff(c_1359,plain,(
    ! [A_130] :
      ( ~ r2_hidden(A_130,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_2'(A_130,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_1355])).

tff(c_1363,plain,(
    ! [A_73] :
      ( ~ r2_hidden(A_73,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_323,c_1359])).

tff(c_1369,plain,(
    ! [A_131] : ~ r2_hidden(A_131,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1363])).

tff(c_1377,plain,(
    a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_1369])).

tff(c_1382,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_1377])).

tff(c_1385,plain,(
    ! [A_132] : ~ r2_hidden(A_132,k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_1396,plain,(
    k2_struct_0('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_1385])).

tff(c_1399,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1396,c_1396,c_76])).

tff(c_1400,plain,(
    u1_struct_0('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1396,c_59])).

tff(c_1488,plain,(
    ! [A_149,B_150] :
      ( k2_orders_2(A_149,B_150) = a_2_1_orders_2(A_149,B_150)
      | ~ m1_subset_1(B_150,k1_zfmisc_1(u1_struct_0(A_149)))
      | ~ l1_orders_2(A_149)
      | ~ v5_orders_2(A_149)
      | ~ v4_orders_2(A_149)
      | ~ v3_orders_2(A_149)
      | v2_struct_0(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1491,plain,(
    ! [B_150] :
      ( k2_orders_2('#skF_4',B_150) = a_2_1_orders_2('#skF_4',B_150)
      | ~ m1_subset_1(B_150,k1_zfmisc_1(k1_xboole_0))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1400,c_1488])).

tff(c_1496,plain,(
    ! [B_150] :
      ( k2_orders_2('#skF_4',B_150) = a_2_1_orders_2('#skF_4',B_150)
      | ~ m1_subset_1(B_150,k1_zfmisc_1(k1_xboole_0))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_1491])).

tff(c_1499,plain,(
    ! [B_151] :
      ( k2_orders_2('#skF_4',B_151) = a_2_1_orders_2('#skF_4',B_151)
      | ~ m1_subset_1(B_151,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1496])).

tff(c_1503,plain,(
    k2_orders_2('#skF_4',k1_xboole_0) = a_2_1_orders_2('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1399,c_1499])).

tff(c_1401,plain,(
    k2_orders_2('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1396,c_36])).

tff(c_1504,plain,(
    a_2_1_orders_2('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1503,c_1401])).

tff(c_1384,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_1398,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1396,c_1384])).

tff(c_1524,plain,(
    ! [A_153,B_154] :
      ( m1_subset_1(k2_orders_2(A_153,B_154),k1_zfmisc_1(u1_struct_0(A_153)))
      | ~ m1_subset_1(B_154,k1_zfmisc_1(u1_struct_0(A_153)))
      | ~ l1_orders_2(A_153)
      | ~ v5_orders_2(A_153)
      | ~ v4_orders_2(A_153)
      | ~ v3_orders_2(A_153)
      | v2_struct_0(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1535,plain,
    ( m1_subset_1(a_2_1_orders_2('#skF_4',k1_xboole_0),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1503,c_1524])).

tff(c_1542,plain,
    ( m1_subset_1(a_2_1_orders_2('#skF_4',k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_1399,c_1400,c_1400,c_1535])).

tff(c_1543,plain,(
    m1_subset_1(a_2_1_orders_2('#skF_4',k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1542])).

tff(c_1560,plain,(
    ! [A_5] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_5,a_2_1_orders_2('#skF_4',k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_1543,c_6])).

tff(c_1565,plain,(
    ! [A_158] : ~ r2_hidden(A_158,a_2_1_orders_2('#skF_4',k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1398,c_1560])).

tff(c_1573,plain,(
    a_2_1_orders_2('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_1565])).

tff(c_1578,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1504,c_1573])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:01:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.43/1.76  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.43/1.77  
% 4.43/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.43/1.77  %$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3
% 4.43/1.77  
% 4.43/1.77  %Foreground sorts:
% 4.43/1.77  
% 4.43/1.77  
% 4.43/1.77  %Background operators:
% 4.43/1.77  
% 4.43/1.77  
% 4.43/1.77  %Foreground operators:
% 4.43/1.77  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.43/1.77  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 4.43/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.43/1.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.43/1.77  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.43/1.77  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 4.43/1.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.43/1.77  tff(a_2_1_orders_2, type, a_2_1_orders_2: ($i * $i) > $i).
% 4.43/1.77  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 4.43/1.77  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.43/1.77  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 4.43/1.77  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 4.43/1.77  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.43/1.77  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.43/1.77  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 4.43/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.43/1.77  tff('#skF_4', type, '#skF_4': $i).
% 4.43/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.43/1.77  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 4.43/1.77  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 4.43/1.77  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.43/1.77  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.43/1.77  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.43/1.77  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.43/1.77  
% 4.43/1.79  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.43/1.79  tff(f_145, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k2_orders_2(A, k2_struct_0(A)) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_orders_2)).
% 4.43/1.79  tff(f_104, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 4.43/1.79  tff(f_50, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 4.43/1.79  tff(f_54, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 4.43/1.79  tff(f_85, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_orders_2(A, B) = a_2_1_orders_2(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_orders_2)).
% 4.43/1.79  tff(f_131, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_1_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, D, E))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_1_orders_2)).
% 4.43/1.79  tff(f_46, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 4.43/1.79  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 4.43/1.79  tff(f_69, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_orders_2)).
% 4.43/1.79  tff(f_100, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_orders_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_orders_2)).
% 4.43/1.79  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.43/1.79  tff(c_38, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.43/1.79  tff(c_22, plain, (![A_22]: (l1_struct_0(A_22) | ~l1_orders_2(A_22))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.43/1.79  tff(c_49, plain, (![A_38]: (u1_struct_0(A_38)=k2_struct_0(A_38) | ~l1_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.43/1.79  tff(c_55, plain, (![A_40]: (u1_struct_0(A_40)=k2_struct_0(A_40) | ~l1_orders_2(A_40))), inference(resolution, [status(thm)], [c_22, c_49])).
% 4.43/1.79  tff(c_59, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_38, c_55])).
% 4.43/1.79  tff(c_10, plain, (![A_9]: (m1_subset_1(k2_struct_0(A_9), k1_zfmisc_1(u1_struct_0(A_9))) | ~l1_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.43/1.79  tff(c_63, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_59, c_10])).
% 4.43/1.79  tff(c_68, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_63])).
% 4.43/1.79  tff(c_71, plain, (~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_22, c_68])).
% 4.43/1.79  tff(c_75, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_71])).
% 4.43/1.79  tff(c_76, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_63])).
% 4.43/1.79  tff(c_46, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.43/1.79  tff(c_44, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.43/1.79  tff(c_42, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.43/1.79  tff(c_40, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.43/1.79  tff(c_117, plain, (![A_61, B_62]: (k2_orders_2(A_61, B_62)=a_2_1_orders_2(A_61, B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_orders_2(A_61) | ~v5_orders_2(A_61) | ~v4_orders_2(A_61) | ~v3_orders_2(A_61) | v2_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.43/1.79  tff(c_120, plain, (![B_62]: (k2_orders_2('#skF_4', B_62)=a_2_1_orders_2('#skF_4', B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_59, c_117])).
% 4.43/1.79  tff(c_125, plain, (![B_62]: (k2_orders_2('#skF_4', B_62)=a_2_1_orders_2('#skF_4', B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_120])).
% 4.43/1.79  tff(c_128, plain, (![B_63]: (k2_orders_2('#skF_4', B_63)=a_2_1_orders_2('#skF_4', B_63) | ~m1_subset_1(B_63, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_46, c_125])).
% 4.43/1.79  tff(c_132, plain, (k2_orders_2('#skF_4', k2_struct_0('#skF_4'))=a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_76, c_128])).
% 4.43/1.79  tff(c_36, plain, (k2_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.43/1.79  tff(c_133, plain, (a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_132, c_36])).
% 4.43/1.79  tff(c_314, plain, (![A_73, B_74, C_75]: (m1_subset_1('#skF_2'(A_73, B_74, C_75), u1_struct_0(B_74)) | ~r2_hidden(A_73, a_2_1_orders_2(B_74, C_75)) | ~m1_subset_1(C_75, k1_zfmisc_1(u1_struct_0(B_74))) | ~l1_orders_2(B_74) | ~v5_orders_2(B_74) | ~v4_orders_2(B_74) | ~v3_orders_2(B_74) | v2_struct_0(B_74))), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.43/1.79  tff(c_319, plain, (![A_73, C_75]: (m1_subset_1('#skF_2'(A_73, '#skF_4', C_75), k2_struct_0('#skF_4')) | ~r2_hidden(A_73, a_2_1_orders_2('#skF_4', C_75)) | ~m1_subset_1(C_75, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_59, c_314])).
% 4.43/1.79  tff(c_322, plain, (![A_73, C_75]: (m1_subset_1('#skF_2'(A_73, '#skF_4', C_75), k2_struct_0('#skF_4')) | ~r2_hidden(A_73, a_2_1_orders_2('#skF_4', C_75)) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_59, c_319])).
% 4.43/1.79  tff(c_323, plain, (![A_73, C_75]: (m1_subset_1('#skF_2'(A_73, '#skF_4', C_75), k2_struct_0('#skF_4')) | ~r2_hidden(A_73, a_2_1_orders_2('#skF_4', C_75)) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_46, c_322])).
% 4.43/1.79  tff(c_6, plain, (![C_7, B_6, A_5]: (~v1_xboole_0(C_7) | ~m1_subset_1(B_6, k1_zfmisc_1(C_7)) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.43/1.79  tff(c_89, plain, (![A_5]: (~v1_xboole_0(k2_struct_0('#skF_4')) | ~r2_hidden(A_5, k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_76, c_6])).
% 4.43/1.79  tff(c_90, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_89])).
% 4.43/1.79  tff(c_4, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.43/1.79  tff(c_1293, plain, (![B_120, A_121, C_122, E_123]: (r2_orders_2(B_120, '#skF_2'(A_121, B_120, C_122), E_123) | ~r2_hidden(E_123, C_122) | ~m1_subset_1(E_123, u1_struct_0(B_120)) | ~r2_hidden(A_121, a_2_1_orders_2(B_120, C_122)) | ~m1_subset_1(C_122, k1_zfmisc_1(u1_struct_0(B_120))) | ~l1_orders_2(B_120) | ~v5_orders_2(B_120) | ~v4_orders_2(B_120) | ~v3_orders_2(B_120) | v2_struct_0(B_120))), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.43/1.79  tff(c_1297, plain, (![A_121, C_122, E_123]: (r2_orders_2('#skF_4', '#skF_2'(A_121, '#skF_4', C_122), E_123) | ~r2_hidden(E_123, C_122) | ~m1_subset_1(E_123, u1_struct_0('#skF_4')) | ~r2_hidden(A_121, a_2_1_orders_2('#skF_4', C_122)) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_59, c_1293])).
% 4.43/1.79  tff(c_1302, plain, (![A_121, C_122, E_123]: (r2_orders_2('#skF_4', '#skF_2'(A_121, '#skF_4', C_122), E_123) | ~r2_hidden(E_123, C_122) | ~m1_subset_1(E_123, k2_struct_0('#skF_4')) | ~r2_hidden(A_121, a_2_1_orders_2('#skF_4', C_122)) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_59, c_1297])).
% 4.43/1.79  tff(c_1305, plain, (![A_124, C_125, E_126]: (r2_orders_2('#skF_4', '#skF_2'(A_124, '#skF_4', C_125), E_126) | ~r2_hidden(E_126, C_125) | ~m1_subset_1(E_126, k2_struct_0('#skF_4')) | ~r2_hidden(A_124, a_2_1_orders_2('#skF_4', C_125)) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_46, c_1302])).
% 4.43/1.79  tff(c_1333, plain, (![A_127, E_128]: (r2_orders_2('#skF_4', '#skF_2'(A_127, '#skF_4', k2_struct_0('#skF_4')), E_128) | ~r2_hidden(E_128, k2_struct_0('#skF_4')) | ~m1_subset_1(E_128, k2_struct_0('#skF_4')) | ~r2_hidden(A_127, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_76, c_1305])).
% 4.43/1.79  tff(c_14, plain, (![A_10, C_16]: (~r2_orders_2(A_10, C_16, C_16) | ~m1_subset_1(C_16, u1_struct_0(A_10)) | ~l1_orders_2(A_10))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.43/1.79  tff(c_1341, plain, (![A_127]: (~m1_subset_1('#skF_2'(A_127, '#skF_4', k2_struct_0('#skF_4')), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~r2_hidden('#skF_2'(A_127, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(A_127, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~r2_hidden(A_127, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_1333, c_14])).
% 4.43/1.79  tff(c_1352, plain, (![A_129]: (~r2_hidden('#skF_2'(A_129, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(A_129, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~r2_hidden(A_129, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_59, c_1341])).
% 4.43/1.79  tff(c_1355, plain, (![A_129]: (~r2_hidden(A_129, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(A_129, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_4, c_1352])).
% 4.43/1.79  tff(c_1359, plain, (![A_130]: (~r2_hidden(A_130, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~m1_subset_1('#skF_2'(A_130, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_90, c_1355])).
% 4.43/1.79  tff(c_1363, plain, (![A_73]: (~r2_hidden(A_73, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_323, c_1359])).
% 4.43/1.79  tff(c_1369, plain, (![A_131]: (~r2_hidden(A_131, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1363])).
% 4.43/1.79  tff(c_1377, plain, (a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_1369])).
% 4.43/1.79  tff(c_1382, plain, $false, inference(negUnitSimplification, [status(thm)], [c_133, c_1377])).
% 4.43/1.79  tff(c_1385, plain, (![A_132]: (~r2_hidden(A_132, k2_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_89])).
% 4.43/1.79  tff(c_1396, plain, (k2_struct_0('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_1385])).
% 4.43/1.79  tff(c_1399, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_1396, c_1396, c_76])).
% 4.43/1.79  tff(c_1400, plain, (u1_struct_0('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1396, c_59])).
% 4.43/1.79  tff(c_1488, plain, (![A_149, B_150]: (k2_orders_2(A_149, B_150)=a_2_1_orders_2(A_149, B_150) | ~m1_subset_1(B_150, k1_zfmisc_1(u1_struct_0(A_149))) | ~l1_orders_2(A_149) | ~v5_orders_2(A_149) | ~v4_orders_2(A_149) | ~v3_orders_2(A_149) | v2_struct_0(A_149))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.43/1.79  tff(c_1491, plain, (![B_150]: (k2_orders_2('#skF_4', B_150)=a_2_1_orders_2('#skF_4', B_150) | ~m1_subset_1(B_150, k1_zfmisc_1(k1_xboole_0)) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1400, c_1488])).
% 4.43/1.79  tff(c_1496, plain, (![B_150]: (k2_orders_2('#skF_4', B_150)=a_2_1_orders_2('#skF_4', B_150) | ~m1_subset_1(B_150, k1_zfmisc_1(k1_xboole_0)) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_1491])).
% 4.43/1.79  tff(c_1499, plain, (![B_151]: (k2_orders_2('#skF_4', B_151)=a_2_1_orders_2('#skF_4', B_151) | ~m1_subset_1(B_151, k1_zfmisc_1(k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_46, c_1496])).
% 4.43/1.79  tff(c_1503, plain, (k2_orders_2('#skF_4', k1_xboole_0)=a_2_1_orders_2('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_1399, c_1499])).
% 4.43/1.79  tff(c_1401, plain, (k2_orders_2('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1396, c_36])).
% 4.43/1.79  tff(c_1504, plain, (a_2_1_orders_2('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1503, c_1401])).
% 4.43/1.79  tff(c_1384, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_89])).
% 4.43/1.79  tff(c_1398, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1396, c_1384])).
% 4.43/1.79  tff(c_1524, plain, (![A_153, B_154]: (m1_subset_1(k2_orders_2(A_153, B_154), k1_zfmisc_1(u1_struct_0(A_153))) | ~m1_subset_1(B_154, k1_zfmisc_1(u1_struct_0(A_153))) | ~l1_orders_2(A_153) | ~v5_orders_2(A_153) | ~v4_orders_2(A_153) | ~v3_orders_2(A_153) | v2_struct_0(A_153))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.43/1.79  tff(c_1535, plain, (m1_subset_1(a_2_1_orders_2('#skF_4', k1_xboole_0), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1503, c_1524])).
% 4.43/1.79  tff(c_1542, plain, (m1_subset_1(a_2_1_orders_2('#skF_4', k1_xboole_0), k1_zfmisc_1(k1_xboole_0)) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_1399, c_1400, c_1400, c_1535])).
% 4.43/1.79  tff(c_1543, plain, (m1_subset_1(a_2_1_orders_2('#skF_4', k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_46, c_1542])).
% 4.43/1.79  tff(c_1560, plain, (![A_5]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_5, a_2_1_orders_2('#skF_4', k1_xboole_0)))), inference(resolution, [status(thm)], [c_1543, c_6])).
% 4.43/1.79  tff(c_1565, plain, (![A_158]: (~r2_hidden(A_158, a_2_1_orders_2('#skF_4', k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_1398, c_1560])).
% 4.43/1.79  tff(c_1573, plain, (a_2_1_orders_2('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_1565])).
% 4.43/1.79  tff(c_1578, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1504, c_1573])).
% 4.43/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.43/1.79  
% 4.43/1.79  Inference rules
% 4.43/1.79  ----------------------
% 4.43/1.79  #Ref     : 0
% 4.43/1.79  #Sup     : 320
% 4.43/1.79  #Fact    : 0
% 4.43/1.79  #Define  : 0
% 4.43/1.79  #Split   : 2
% 4.43/1.79  #Chain   : 0
% 4.43/1.79  #Close   : 0
% 4.43/1.79  
% 4.43/1.79  Ordering : KBO
% 4.43/1.79  
% 4.43/1.79  Simplification rules
% 4.43/1.79  ----------------------
% 4.43/1.79  #Subsume      : 75
% 4.43/1.79  #Demod        : 894
% 4.43/1.79  #Tautology    : 75
% 4.43/1.79  #SimpNegUnit  : 95
% 4.43/1.79  #BackRed      : 9
% 4.43/1.79  
% 4.43/1.79  #Partial instantiations: 0
% 4.43/1.79  #Strategies tried      : 1
% 4.43/1.79  
% 4.43/1.79  Timing (in seconds)
% 4.43/1.79  ----------------------
% 4.43/1.79  Preprocessing        : 0.33
% 4.43/1.79  Parsing              : 0.17
% 4.43/1.79  CNF conversion       : 0.02
% 4.43/1.79  Main loop            : 0.65
% 4.43/1.79  Inferencing          : 0.19
% 4.43/1.79  Reduction            : 0.19
% 4.43/1.79  Demodulation         : 0.14
% 4.43/1.79  BG Simplification    : 0.03
% 4.43/1.79  Subsumption          : 0.20
% 4.43/1.79  Abstraction          : 0.03
% 4.43/1.79  MUC search           : 0.00
% 4.43/1.80  Cooper               : 0.00
% 4.43/1.80  Total                : 1.02
% 4.43/1.80  Index Insertion      : 0.00
% 4.43/1.80  Index Deletion       : 0.00
% 4.43/1.80  Index Matching       : 0.00
% 4.43/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
