%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:30 EST 2020

% Result     : Theorem 3.91s
% Output     : CNFRefutation 3.91s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 365 expanded)
%              Number of leaves         :   35 ( 143 expanded)
%              Depth                    :   17
%              Number of atoms          :  210 ( 951 expanded)
%              Number of equality atoms :   18 ( 160 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_150,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => k2_orders_2(A,k2_struct_0(A)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_orders_2)).

tff(f_109,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_59,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_90,axiom,(
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

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ~ ( B != k1_xboole_0
          & ! [C] :
              ( m1_subset_1(C,A)
             => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_136,axiom,(
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

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_74,axiom,(
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

tff(f_105,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_orders_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_orders_2)).

tff(c_40,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_24,plain,(
    ! [A_21] :
      ( l1_struct_0(A_21)
      | ~ l1_orders_2(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_50,plain,(
    ! [A_36] :
      ( u1_struct_0(A_36) = k2_struct_0(A_36)
      | ~ l1_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_55,plain,(
    ! [A_37] :
      ( u1_struct_0(A_37) = k2_struct_0(A_37)
      | ~ l1_orders_2(A_37) ) ),
    inference(resolution,[status(thm)],[c_24,c_50])).

tff(c_59,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_55])).

tff(c_64,plain,(
    ! [A_38] :
      ( ~ v1_xboole_0(u1_struct_0(A_38))
      | ~ l1_struct_0(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_67,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_64])).

tff(c_68,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_67])).

tff(c_69,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_72,plain,(
    ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_69])).

tff(c_76,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_72])).

tff(c_78,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_84,plain,(
    ! [A_39] :
      ( m1_subset_1(k2_struct_0(A_39),k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ l1_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_87,plain,
    ( m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ l1_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_84])).

tff(c_89,plain,(
    m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_87])).

tff(c_46,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_44,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_42,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_109,plain,(
    ! [A_56,B_57] :
      ( k2_orders_2(A_56,B_57) = a_2_1_orders_2(A_56,B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_orders_2(A_56)
      | ~ v5_orders_2(A_56)
      | ~ v4_orders_2(A_56)
      | ~ v3_orders_2(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_119,plain,(
    ! [B_57] :
      ( k2_orders_2('#skF_4',B_57) = a_2_1_orders_2('#skF_4',B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_109])).

tff(c_123,plain,(
    ! [B_57] :
      ( k2_orders_2('#skF_4',B_57) = a_2_1_orders_2('#skF_4',B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_119])).

tff(c_136,plain,(
    ! [B_60] :
      ( k2_orders_2('#skF_4',B_60) = a_2_1_orders_2('#skF_4',B_60)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_123])).

tff(c_145,plain,(
    k2_orders_2('#skF_4',k2_struct_0('#skF_4')) = a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_89,c_136])).

tff(c_38,plain,(
    k2_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_146,plain,(
    a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_38])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | k1_xboole_0 = B_2
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_339,plain,(
    ! [A_68,B_69,C_70] :
      ( m1_subset_1('#skF_2'(A_68,B_69,C_70),u1_struct_0(B_69))
      | ~ r2_hidden(A_68,a_2_1_orders_2(B_69,C_70))
      | ~ m1_subset_1(C_70,k1_zfmisc_1(u1_struct_0(B_69)))
      | ~ l1_orders_2(B_69)
      | ~ v5_orders_2(B_69)
      | ~ v4_orders_2(B_69)
      | ~ v3_orders_2(B_69)
      | v2_struct_0(B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_344,plain,(
    ! [A_68,C_70] :
      ( m1_subset_1('#skF_2'(A_68,'#skF_4',C_70),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_68,a_2_1_orders_2('#skF_4',C_70))
      | ~ m1_subset_1(C_70,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_339])).

tff(c_347,plain,(
    ! [A_68,C_70] :
      ( m1_subset_1('#skF_2'(A_68,'#skF_4',C_70),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_68,a_2_1_orders_2('#skF_4',C_70))
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_59,c_344])).

tff(c_348,plain,(
    ! [A_68,C_70] :
      ( m1_subset_1('#skF_2'(A_68,'#skF_4',C_70),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_68,a_2_1_orders_2('#skF_4',C_70))
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_347])).

tff(c_77,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( r2_hidden(A_4,B_5)
      | v1_xboole_0(B_5)
      | ~ m1_subset_1(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_953,plain,(
    ! [B_109,A_110,C_111,E_112] :
      ( r2_orders_2(B_109,'#skF_2'(A_110,B_109,C_111),E_112)
      | ~ r2_hidden(E_112,C_111)
      | ~ m1_subset_1(E_112,u1_struct_0(B_109))
      | ~ r2_hidden(A_110,a_2_1_orders_2(B_109,C_111))
      | ~ m1_subset_1(C_111,k1_zfmisc_1(u1_struct_0(B_109)))
      | ~ l1_orders_2(B_109)
      | ~ v5_orders_2(B_109)
      | ~ v4_orders_2(B_109)
      | ~ v3_orders_2(B_109)
      | v2_struct_0(B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_962,plain,(
    ! [A_110,C_111,E_112] :
      ( r2_orders_2('#skF_4','#skF_2'(A_110,'#skF_4',C_111),E_112)
      | ~ r2_hidden(E_112,C_111)
      | ~ m1_subset_1(E_112,u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_110,a_2_1_orders_2('#skF_4',C_111))
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_953])).

tff(c_967,plain,(
    ! [A_110,C_111,E_112] :
      ( r2_orders_2('#skF_4','#skF_2'(A_110,'#skF_4',C_111),E_112)
      | ~ r2_hidden(E_112,C_111)
      | ~ m1_subset_1(E_112,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_110,a_2_1_orders_2('#skF_4',C_111))
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_59,c_962])).

tff(c_969,plain,(
    ! [A_113,C_114,E_115] :
      ( r2_orders_2('#skF_4','#skF_2'(A_113,'#skF_4',C_114),E_115)
      | ~ r2_hidden(E_115,C_114)
      | ~ m1_subset_1(E_115,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_113,a_2_1_orders_2('#skF_4',C_114))
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_967])).

tff(c_1001,plain,(
    ! [A_116,E_117] :
      ( r2_orders_2('#skF_4','#skF_2'(A_116,'#skF_4',k2_struct_0('#skF_4')),E_117)
      | ~ r2_hidden(E_117,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_117,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_116,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_89,c_969])).

tff(c_16,plain,(
    ! [A_9,C_15] :
      ( ~ r2_orders_2(A_9,C_15,C_15)
      | ~ m1_subset_1(C_15,u1_struct_0(A_9))
      | ~ l1_orders_2(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1009,plain,(
    ! [A_116] :
      ( ~ m1_subset_1('#skF_2'(A_116,'#skF_4',k2_struct_0('#skF_4')),u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ r2_hidden('#skF_2'(A_116,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_116,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_116,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_1001,c_16])).

tff(c_1020,plain,(
    ! [A_118] :
      ( ~ r2_hidden('#skF_2'(A_118,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_118,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_118,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_59,c_1009])).

tff(c_1023,plain,(
    ! [A_118] :
      ( ~ r2_hidden(A_118,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_118,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_6,c_1020])).

tff(c_1028,plain,(
    ! [A_119] :
      ( ~ r2_hidden(A_119,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_2'(A_119,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_1023])).

tff(c_1032,plain,(
    ! [A_68] :
      ( ~ r2_hidden(A_68,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_348,c_1028])).

tff(c_1038,plain,(
    ! [A_120] : ~ r2_hidden(A_120,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_1032])).

tff(c_1042,plain,(
    ! [A_1] :
      ( a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0
      | ~ m1_subset_1(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')),k1_zfmisc_1(A_1)) ) ),
    inference(resolution,[status(thm)],[c_2,c_1038])).

tff(c_1049,plain,(
    ! [A_1] : ~ m1_subset_1(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')),k1_zfmisc_1(A_1)) ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_1042])).

tff(c_22,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(k2_orders_2(A_19,B_20),k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_orders_2(A_19)
      | ~ v5_orders_2(A_19)
      | ~ v4_orders_2(A_19)
      | ~ v3_orders_2(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_150,plain,
    ( m1_subset_1(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_22])).

tff(c_154,plain,
    ( m1_subset_1(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_89,c_59,c_59,c_150])).

tff(c_155,plain,(
    m1_subset_1(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_154])).

tff(c_1053,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1049,c_155])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:18:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.91/1.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.91/1.64  
% 3.91/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.91/1.65  %$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 3.91/1.65  
% 3.91/1.65  %Foreground sorts:
% 3.91/1.65  
% 3.91/1.65  
% 3.91/1.65  %Background operators:
% 3.91/1.65  
% 3.91/1.65  
% 3.91/1.65  %Foreground operators:
% 3.91/1.65  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.91/1.65  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.91/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.91/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.91/1.65  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.91/1.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.91/1.65  tff(a_2_1_orders_2, type, a_2_1_orders_2: ($i * $i) > $i).
% 3.91/1.65  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 3.91/1.65  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.91/1.65  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.91/1.65  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.91/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.91/1.65  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.91/1.65  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.91/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.91/1.65  tff('#skF_4', type, '#skF_4': $i).
% 3.91/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.91/1.65  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 3.91/1.65  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.91/1.65  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.91/1.65  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.91/1.65  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.91/1.65  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.91/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.91/1.65  
% 3.91/1.66  tff(f_150, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k2_orders_2(A, k2_struct_0(A)) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_orders_2)).
% 3.91/1.66  tff(f_109, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 3.91/1.66  tff(f_47, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.91/1.66  tff(f_59, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.91/1.66  tff(f_51, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 3.91/1.66  tff(f_90, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_orders_2(A, B) = a_2_1_orders_2(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_orders_2)).
% 3.91/1.66  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_subset_1)).
% 3.91/1.66  tff(f_136, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_1_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, D, E))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_1_orders_2)).
% 3.91/1.66  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.91/1.66  tff(f_74, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_orders_2)).
% 3.91/1.66  tff(f_105, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_orders_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_orders_2)).
% 3.91/1.66  tff(c_40, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.91/1.66  tff(c_24, plain, (![A_21]: (l1_struct_0(A_21) | ~l1_orders_2(A_21))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.91/1.66  tff(c_48, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.91/1.66  tff(c_50, plain, (![A_36]: (u1_struct_0(A_36)=k2_struct_0(A_36) | ~l1_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.91/1.66  tff(c_55, plain, (![A_37]: (u1_struct_0(A_37)=k2_struct_0(A_37) | ~l1_orders_2(A_37))), inference(resolution, [status(thm)], [c_24, c_50])).
% 3.91/1.66  tff(c_59, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_40, c_55])).
% 3.91/1.66  tff(c_64, plain, (![A_38]: (~v1_xboole_0(u1_struct_0(A_38)) | ~l1_struct_0(A_38) | v2_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.91/1.66  tff(c_67, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_59, c_64])).
% 3.91/1.66  tff(c_68, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_48, c_67])).
% 3.91/1.66  tff(c_69, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_68])).
% 3.91/1.66  tff(c_72, plain, (~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_24, c_69])).
% 3.91/1.66  tff(c_76, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_72])).
% 3.91/1.66  tff(c_78, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_68])).
% 3.91/1.66  tff(c_84, plain, (![A_39]: (m1_subset_1(k2_struct_0(A_39), k1_zfmisc_1(u1_struct_0(A_39))) | ~l1_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.91/1.66  tff(c_87, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_59, c_84])).
% 3.91/1.66  tff(c_89, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_87])).
% 3.91/1.66  tff(c_46, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.91/1.66  tff(c_44, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.91/1.66  tff(c_42, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.91/1.66  tff(c_109, plain, (![A_56, B_57]: (k2_orders_2(A_56, B_57)=a_2_1_orders_2(A_56, B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_orders_2(A_56) | ~v5_orders_2(A_56) | ~v4_orders_2(A_56) | ~v3_orders_2(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.91/1.66  tff(c_119, plain, (![B_57]: (k2_orders_2('#skF_4', B_57)=a_2_1_orders_2('#skF_4', B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_59, c_109])).
% 3.91/1.66  tff(c_123, plain, (![B_57]: (k2_orders_2('#skF_4', B_57)=a_2_1_orders_2('#skF_4', B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_119])).
% 3.91/1.66  tff(c_136, plain, (![B_60]: (k2_orders_2('#skF_4', B_60)=a_2_1_orders_2('#skF_4', B_60) | ~m1_subset_1(B_60, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_48, c_123])).
% 3.91/1.66  tff(c_145, plain, (k2_orders_2('#skF_4', k2_struct_0('#skF_4'))=a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_89, c_136])).
% 3.91/1.66  tff(c_38, plain, (k2_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.91/1.66  tff(c_146, plain, (a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_145, c_38])).
% 3.91/1.66  tff(c_2, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | k1_xboole_0=B_2 | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.91/1.66  tff(c_339, plain, (![A_68, B_69, C_70]: (m1_subset_1('#skF_2'(A_68, B_69, C_70), u1_struct_0(B_69)) | ~r2_hidden(A_68, a_2_1_orders_2(B_69, C_70)) | ~m1_subset_1(C_70, k1_zfmisc_1(u1_struct_0(B_69))) | ~l1_orders_2(B_69) | ~v5_orders_2(B_69) | ~v4_orders_2(B_69) | ~v3_orders_2(B_69) | v2_struct_0(B_69))), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.91/1.66  tff(c_344, plain, (![A_68, C_70]: (m1_subset_1('#skF_2'(A_68, '#skF_4', C_70), k2_struct_0('#skF_4')) | ~r2_hidden(A_68, a_2_1_orders_2('#skF_4', C_70)) | ~m1_subset_1(C_70, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_59, c_339])).
% 3.91/1.66  tff(c_347, plain, (![A_68, C_70]: (m1_subset_1('#skF_2'(A_68, '#skF_4', C_70), k2_struct_0('#skF_4')) | ~r2_hidden(A_68, a_2_1_orders_2('#skF_4', C_70)) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_59, c_344])).
% 3.91/1.66  tff(c_348, plain, (![A_68, C_70]: (m1_subset_1('#skF_2'(A_68, '#skF_4', C_70), k2_struct_0('#skF_4')) | ~r2_hidden(A_68, a_2_1_orders_2('#skF_4', C_70)) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_48, c_347])).
% 3.91/1.66  tff(c_77, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_68])).
% 3.91/1.66  tff(c_6, plain, (![A_4, B_5]: (r2_hidden(A_4, B_5) | v1_xboole_0(B_5) | ~m1_subset_1(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.91/1.66  tff(c_953, plain, (![B_109, A_110, C_111, E_112]: (r2_orders_2(B_109, '#skF_2'(A_110, B_109, C_111), E_112) | ~r2_hidden(E_112, C_111) | ~m1_subset_1(E_112, u1_struct_0(B_109)) | ~r2_hidden(A_110, a_2_1_orders_2(B_109, C_111)) | ~m1_subset_1(C_111, k1_zfmisc_1(u1_struct_0(B_109))) | ~l1_orders_2(B_109) | ~v5_orders_2(B_109) | ~v4_orders_2(B_109) | ~v3_orders_2(B_109) | v2_struct_0(B_109))), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.91/1.66  tff(c_962, plain, (![A_110, C_111, E_112]: (r2_orders_2('#skF_4', '#skF_2'(A_110, '#skF_4', C_111), E_112) | ~r2_hidden(E_112, C_111) | ~m1_subset_1(E_112, u1_struct_0('#skF_4')) | ~r2_hidden(A_110, a_2_1_orders_2('#skF_4', C_111)) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_59, c_953])).
% 3.91/1.66  tff(c_967, plain, (![A_110, C_111, E_112]: (r2_orders_2('#skF_4', '#skF_2'(A_110, '#skF_4', C_111), E_112) | ~r2_hidden(E_112, C_111) | ~m1_subset_1(E_112, k2_struct_0('#skF_4')) | ~r2_hidden(A_110, a_2_1_orders_2('#skF_4', C_111)) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_59, c_962])).
% 3.91/1.66  tff(c_969, plain, (![A_113, C_114, E_115]: (r2_orders_2('#skF_4', '#skF_2'(A_113, '#skF_4', C_114), E_115) | ~r2_hidden(E_115, C_114) | ~m1_subset_1(E_115, k2_struct_0('#skF_4')) | ~r2_hidden(A_113, a_2_1_orders_2('#skF_4', C_114)) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_48, c_967])).
% 3.91/1.66  tff(c_1001, plain, (![A_116, E_117]: (r2_orders_2('#skF_4', '#skF_2'(A_116, '#skF_4', k2_struct_0('#skF_4')), E_117) | ~r2_hidden(E_117, k2_struct_0('#skF_4')) | ~m1_subset_1(E_117, k2_struct_0('#skF_4')) | ~r2_hidden(A_116, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_89, c_969])).
% 3.91/1.66  tff(c_16, plain, (![A_9, C_15]: (~r2_orders_2(A_9, C_15, C_15) | ~m1_subset_1(C_15, u1_struct_0(A_9)) | ~l1_orders_2(A_9))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.91/1.66  tff(c_1009, plain, (![A_116]: (~m1_subset_1('#skF_2'(A_116, '#skF_4', k2_struct_0('#skF_4')), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~r2_hidden('#skF_2'(A_116, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(A_116, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~r2_hidden(A_116, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_1001, c_16])).
% 3.91/1.66  tff(c_1020, plain, (![A_118]: (~r2_hidden('#skF_2'(A_118, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(A_118, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~r2_hidden(A_118, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_59, c_1009])).
% 3.91/1.66  tff(c_1023, plain, (![A_118]: (~r2_hidden(A_118, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(A_118, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_6, c_1020])).
% 3.91/1.66  tff(c_1028, plain, (![A_119]: (~r2_hidden(A_119, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~m1_subset_1('#skF_2'(A_119, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_77, c_1023])).
% 3.91/1.66  tff(c_1032, plain, (![A_68]: (~r2_hidden(A_68, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_348, c_1028])).
% 3.91/1.66  tff(c_1038, plain, (![A_120]: (~r2_hidden(A_120, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_1032])).
% 3.91/1.66  tff(c_1042, plain, (![A_1]: (a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0 | ~m1_subset_1(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')), k1_zfmisc_1(A_1)))), inference(resolution, [status(thm)], [c_2, c_1038])).
% 3.91/1.66  tff(c_1049, plain, (![A_1]: (~m1_subset_1(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')), k1_zfmisc_1(A_1)))), inference(negUnitSimplification, [status(thm)], [c_146, c_1042])).
% 3.91/1.66  tff(c_22, plain, (![A_19, B_20]: (m1_subset_1(k2_orders_2(A_19, B_20), k1_zfmisc_1(u1_struct_0(A_19))) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_orders_2(A_19) | ~v5_orders_2(A_19) | ~v4_orders_2(A_19) | ~v3_orders_2(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.91/1.66  tff(c_150, plain, (m1_subset_1(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_145, c_22])).
% 3.91/1.66  tff(c_154, plain, (m1_subset_1(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')), k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_89, c_59, c_59, c_150])).
% 3.91/1.66  tff(c_155, plain, (m1_subset_1(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_48, c_154])).
% 3.91/1.66  tff(c_1053, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1049, c_155])).
% 3.91/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.91/1.66  
% 3.91/1.66  Inference rules
% 3.91/1.66  ----------------------
% 3.91/1.66  #Ref     : 0
% 3.91/1.66  #Sup     : 221
% 3.91/1.66  #Fact    : 0
% 3.91/1.66  #Define  : 0
% 3.91/1.67  #Split   : 4
% 3.91/1.67  #Chain   : 0
% 3.91/1.67  #Close   : 0
% 3.91/1.67  
% 3.91/1.67  Ordering : KBO
% 3.91/1.67  
% 3.91/1.67  Simplification rules
% 3.91/1.67  ----------------------
% 3.91/1.67  #Subsume      : 10
% 3.91/1.67  #Demod        : 463
% 3.91/1.67  #Tautology    : 58
% 3.91/1.67  #SimpNegUnit  : 43
% 3.91/1.67  #BackRed      : 4
% 3.91/1.67  
% 3.91/1.67  #Partial instantiations: 0
% 3.91/1.67  #Strategies tried      : 1
% 3.91/1.67  
% 3.91/1.67  Timing (in seconds)
% 3.91/1.67  ----------------------
% 3.91/1.67  Preprocessing        : 0.35
% 3.91/1.67  Parsing              : 0.18
% 3.91/1.67  CNF conversion       : 0.03
% 3.91/1.67  Main loop            : 0.55
% 3.91/1.67  Inferencing          : 0.19
% 3.91/1.67  Reduction            : 0.18
% 3.91/1.67  Demodulation         : 0.13
% 3.91/1.67  BG Simplification    : 0.03
% 3.91/1.67  Subsumption          : 0.10
% 3.91/1.67  Abstraction          : 0.04
% 3.91/1.67  MUC search           : 0.00
% 3.91/1.67  Cooper               : 0.00
% 3.91/1.67  Total                : 0.94
% 3.91/1.67  Index Insertion      : 0.00
% 3.91/1.67  Index Deletion       : 0.00
% 3.91/1.67  Index Matching       : 0.00
% 3.91/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
