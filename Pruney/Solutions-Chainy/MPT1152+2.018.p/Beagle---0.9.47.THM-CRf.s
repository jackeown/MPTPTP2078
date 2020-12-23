%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:30 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 2.90s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 740 expanded)
%              Number of leaves         :   36 ( 284 expanded)
%              Depth                    :   18
%              Number of atoms          :  220 (2156 expanded)
%              Number of equality atoms :   32 ( 440 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    5 (   2 average)

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

tff(f_131,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => k2_orders_2(A,k2_struct_0(A)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_orders_2)).

tff(f_90,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_55,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_35,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_37,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_86,axiom,(
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

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_117,axiom,(
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

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_70,axiom,(
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

tff(c_38,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_22,plain,(
    ! [A_19] :
      ( l1_struct_0(A_19)
      | ~ l1_orders_2(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_59,plain,(
    ! [A_36] :
      ( u1_struct_0(A_36) = k2_struct_0(A_36)
      | ~ l1_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_65,plain,(
    ! [A_38] :
      ( u1_struct_0(A_38) = k2_struct_0(A_38)
      | ~ l1_orders_2(A_38) ) ),
    inference(resolution,[status(thm)],[c_22,c_59])).

tff(c_69,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_65])).

tff(c_74,plain,(
    ! [A_39] :
      ( ~ v1_xboole_0(u1_struct_0(A_39))
      | ~ l1_struct_0(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_77,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_74])).

tff(c_78,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_77])).

tff(c_79,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_83,plain,(
    ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_79])).

tff(c_87,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_83])).

tff(c_88,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_4,plain,(
    ! [A_3] : k2_subset_1(A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_4] : m1_subset_1(k2_subset_1(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_47,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_44,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_42,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_40,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_104,plain,(
    ! [A_54,B_55] :
      ( k2_orders_2(A_54,B_55) = a_2_1_orders_2(A_54,B_55)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ l1_orders_2(A_54)
      | ~ v5_orders_2(A_54)
      | ~ v4_orders_2(A_54)
      | ~ v3_orders_2(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_107,plain,(
    ! [B_55] :
      ( k2_orders_2('#skF_4',B_55) = a_2_1_orders_2('#skF_4',B_55)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_104])).

tff(c_113,plain,(
    ! [B_55] :
      ( k2_orders_2('#skF_4',B_55) = a_2_1_orders_2('#skF_4',B_55)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_107])).

tff(c_125,plain,(
    ! [B_59] :
      ( k2_orders_2('#skF_4',B_59) = a_2_1_orders_2('#skF_4',B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_113])).

tff(c_130,plain,(
    k2_orders_2('#skF_4',k2_struct_0('#skF_4')) = a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_47,c_125])).

tff(c_36,plain,(
    k2_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_131,plain,(
    a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_36])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_116,plain,(
    ! [A_56,B_57,C_58] :
      ( '#skF_2'(A_56,B_57,C_58) = A_56
      | ~ r2_hidden(A_56,a_2_1_orders_2(B_57,C_58))
      | ~ m1_subset_1(C_58,k1_zfmisc_1(u1_struct_0(B_57)))
      | ~ l1_orders_2(B_57)
      | ~ v5_orders_2(B_57)
      | ~ v4_orders_2(B_57)
      | ~ v3_orders_2(B_57)
      | v2_struct_0(B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_222,plain,(
    ! [B_84,C_85] :
      ( '#skF_2'('#skF_1'(a_2_1_orders_2(B_84,C_85)),B_84,C_85) = '#skF_1'(a_2_1_orders_2(B_84,C_85))
      | ~ m1_subset_1(C_85,k1_zfmisc_1(u1_struct_0(B_84)))
      | ~ l1_orders_2(B_84)
      | ~ v5_orders_2(B_84)
      | ~ v4_orders_2(B_84)
      | ~ v3_orders_2(B_84)
      | v2_struct_0(B_84)
      | a_2_1_orders_2(B_84,C_85) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_116])).

tff(c_224,plain,(
    ! [C_85] :
      ( '#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4',C_85)),'#skF_4',C_85) = '#skF_1'(a_2_1_orders_2('#skF_4',C_85))
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | a_2_1_orders_2('#skF_4',C_85) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_222])).

tff(c_229,plain,(
    ! [C_85] :
      ( '#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4',C_85)),'#skF_4',C_85) = '#skF_1'(a_2_1_orders_2('#skF_4',C_85))
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | a_2_1_orders_2('#skF_4',C_85) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_224])).

tff(c_232,plain,(
    ! [C_86] :
      ( '#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4',C_86)),'#skF_4',C_86) = '#skF_1'(a_2_1_orders_2('#skF_4',C_86))
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | a_2_1_orders_2('#skF_4',C_86) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_229])).

tff(c_235,plain,
    ( '#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),'#skF_4',k2_struct_0('#skF_4')) = '#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
    | a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_47,c_232])).

tff(c_238,plain,(
    '#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),'#skF_4',k2_struct_0('#skF_4')) = '#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_235])).

tff(c_136,plain,(
    ! [A_60,B_61,C_62] :
      ( m1_subset_1('#skF_2'(A_60,B_61,C_62),u1_struct_0(B_61))
      | ~ r2_hidden(A_60,a_2_1_orders_2(B_61,C_62))
      | ~ m1_subset_1(C_62,k1_zfmisc_1(u1_struct_0(B_61)))
      | ~ l1_orders_2(B_61)
      | ~ v5_orders_2(B_61)
      | ~ v4_orders_2(B_61)
      | ~ v3_orders_2(B_61)
      | v2_struct_0(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_141,plain,(
    ! [A_60,C_62] :
      ( m1_subset_1('#skF_2'(A_60,'#skF_4',C_62),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_60,a_2_1_orders_2('#skF_4',C_62))
      | ~ m1_subset_1(C_62,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_136])).

tff(c_144,plain,(
    ! [A_60,C_62] :
      ( m1_subset_1('#skF_2'(A_60,'#skF_4',C_62),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_60,a_2_1_orders_2('#skF_4',C_62))
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_69,c_141])).

tff(c_145,plain,(
    ! [A_60,C_62] :
      ( m1_subset_1('#skF_2'(A_60,'#skF_4',C_62),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_60,a_2_1_orders_2('#skF_4',C_62))
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_144])).

tff(c_242,plain,
    ( m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4'))
    | ~ r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
    | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_145])).

tff(c_249,plain,
    ( m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4'))
    | ~ r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_242])).

tff(c_255,plain,(
    ~ r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_249])).

tff(c_261,plain,(
    a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_255])).

tff(c_267,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_261])).

tff(c_268,plain,(
    m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_249])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r2_hidden(A_5,B_6)
      | v1_xboole_0(B_6)
      | ~ m1_subset_1(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_269,plain,(
    r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_249])).

tff(c_340,plain,(
    ! [B_97,A_98,C_99,E_100] :
      ( r2_orders_2(B_97,'#skF_2'(A_98,B_97,C_99),E_100)
      | ~ r2_hidden(E_100,C_99)
      | ~ m1_subset_1(E_100,u1_struct_0(B_97))
      | ~ r2_hidden(A_98,a_2_1_orders_2(B_97,C_99))
      | ~ m1_subset_1(C_99,k1_zfmisc_1(u1_struct_0(B_97)))
      | ~ l1_orders_2(B_97)
      | ~ v5_orders_2(B_97)
      | ~ v4_orders_2(B_97)
      | ~ v3_orders_2(B_97)
      | v2_struct_0(B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_342,plain,(
    ! [A_98,C_99,E_100] :
      ( r2_orders_2('#skF_4','#skF_2'(A_98,'#skF_4',C_99),E_100)
      | ~ r2_hidden(E_100,C_99)
      | ~ m1_subset_1(E_100,u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_98,a_2_1_orders_2('#skF_4',C_99))
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_340])).

tff(c_347,plain,(
    ! [A_98,C_99,E_100] :
      ( r2_orders_2('#skF_4','#skF_2'(A_98,'#skF_4',C_99),E_100)
      | ~ r2_hidden(E_100,C_99)
      | ~ m1_subset_1(E_100,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_98,a_2_1_orders_2('#skF_4',C_99))
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_69,c_342])).

tff(c_350,plain,(
    ! [A_101,C_102,E_103] :
      ( r2_orders_2('#skF_4','#skF_2'(A_101,'#skF_4',C_102),E_103)
      | ~ r2_hidden(E_103,C_102)
      | ~ m1_subset_1(E_103,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_101,a_2_1_orders_2('#skF_4',C_102))
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_347])).

tff(c_355,plain,(
    ! [A_104,E_105] :
      ( r2_orders_2('#skF_4','#skF_2'(A_104,'#skF_4',k2_struct_0('#skF_4')),E_105)
      | ~ r2_hidden(E_105,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_105,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_104,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_47,c_350])).

tff(c_366,plain,(
    ! [E_105] :
      ( r2_orders_2('#skF_4','#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),E_105)
      | ~ r2_hidden(E_105,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_105,k2_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_355])).

tff(c_379,plain,(
    ! [E_106] :
      ( r2_orders_2('#skF_4','#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),E_106)
      | ~ r2_hidden(E_106,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_106,k2_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_366])).

tff(c_16,plain,(
    ! [A_9,C_15] :
      ( ~ r2_orders_2(A_9,C_15,C_15)
      | ~ m1_subset_1(C_15,u1_struct_0(A_9))
      | ~ l1_orders_2(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_387,plain,
    ( ~ m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4')
    | ~ r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_379,c_16])).

tff(c_397,plain,(
    ~ r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_38,c_268,c_69,c_387])).

tff(c_414,plain,
    ( v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_8,c_397])).

tff(c_417,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_414])).

tff(c_419,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_417])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:19:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.68/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.39  
% 2.68/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.39  %$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3
% 2.68/1.39  
% 2.68/1.39  %Foreground sorts:
% 2.68/1.39  
% 2.68/1.39  
% 2.68/1.39  %Background operators:
% 2.68/1.39  
% 2.68/1.39  
% 2.68/1.39  %Foreground operators:
% 2.68/1.39  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.68/1.39  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.68/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.68/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.68/1.39  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.68/1.39  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.68/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.68/1.39  tff(a_2_1_orders_2, type, a_2_1_orders_2: ($i * $i) > $i).
% 2.68/1.39  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 2.68/1.39  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.68/1.39  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.68/1.39  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.68/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.68/1.39  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.68/1.39  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.68/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.68/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.68/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.68/1.39  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 2.68/1.39  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.68/1.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.68/1.39  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.68/1.39  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.68/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.68/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.68/1.39  
% 2.90/1.41  tff(f_131, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k2_orders_2(A, k2_struct_0(A)) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_orders_2)).
% 2.90/1.41  tff(f_90, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.90/1.41  tff(f_47, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.90/1.41  tff(f_55, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.90/1.41  tff(f_35, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.90/1.41  tff(f_37, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.90/1.41  tff(f_86, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_orders_2(A, B) = a_2_1_orders_2(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_orders_2)).
% 2.90/1.41  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.90/1.41  tff(f_117, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_1_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, D, E))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_1_orders_2)).
% 2.90/1.41  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.90/1.41  tff(f_70, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_orders_2)).
% 2.90/1.41  tff(c_38, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.90/1.41  tff(c_22, plain, (![A_19]: (l1_struct_0(A_19) | ~l1_orders_2(A_19))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.90/1.41  tff(c_46, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.90/1.41  tff(c_59, plain, (![A_36]: (u1_struct_0(A_36)=k2_struct_0(A_36) | ~l1_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.90/1.41  tff(c_65, plain, (![A_38]: (u1_struct_0(A_38)=k2_struct_0(A_38) | ~l1_orders_2(A_38))), inference(resolution, [status(thm)], [c_22, c_59])).
% 2.90/1.41  tff(c_69, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_38, c_65])).
% 2.90/1.41  tff(c_74, plain, (![A_39]: (~v1_xboole_0(u1_struct_0(A_39)) | ~l1_struct_0(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.90/1.41  tff(c_77, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_69, c_74])).
% 2.90/1.41  tff(c_78, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_46, c_77])).
% 2.90/1.41  tff(c_79, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_78])).
% 2.90/1.41  tff(c_83, plain, (~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_22, c_79])).
% 2.90/1.41  tff(c_87, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_83])).
% 2.90/1.41  tff(c_88, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_78])).
% 2.90/1.41  tff(c_4, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.90/1.41  tff(c_6, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.90/1.41  tff(c_47, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 2.90/1.41  tff(c_44, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.90/1.41  tff(c_42, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.90/1.41  tff(c_40, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.90/1.41  tff(c_104, plain, (![A_54, B_55]: (k2_orders_2(A_54, B_55)=a_2_1_orders_2(A_54, B_55) | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0(A_54))) | ~l1_orders_2(A_54) | ~v5_orders_2(A_54) | ~v4_orders_2(A_54) | ~v3_orders_2(A_54) | v2_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.90/1.41  tff(c_107, plain, (![B_55]: (k2_orders_2('#skF_4', B_55)=a_2_1_orders_2('#skF_4', B_55) | ~m1_subset_1(B_55, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_69, c_104])).
% 2.90/1.41  tff(c_113, plain, (![B_55]: (k2_orders_2('#skF_4', B_55)=a_2_1_orders_2('#skF_4', B_55) | ~m1_subset_1(B_55, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_107])).
% 2.90/1.41  tff(c_125, plain, (![B_59]: (k2_orders_2('#skF_4', B_59)=a_2_1_orders_2('#skF_4', B_59) | ~m1_subset_1(B_59, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_46, c_113])).
% 2.90/1.41  tff(c_130, plain, (k2_orders_2('#skF_4', k2_struct_0('#skF_4'))=a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_47, c_125])).
% 2.90/1.41  tff(c_36, plain, (k2_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.90/1.41  tff(c_131, plain, (a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_130, c_36])).
% 2.90/1.41  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.90/1.41  tff(c_116, plain, (![A_56, B_57, C_58]: ('#skF_2'(A_56, B_57, C_58)=A_56 | ~r2_hidden(A_56, a_2_1_orders_2(B_57, C_58)) | ~m1_subset_1(C_58, k1_zfmisc_1(u1_struct_0(B_57))) | ~l1_orders_2(B_57) | ~v5_orders_2(B_57) | ~v4_orders_2(B_57) | ~v3_orders_2(B_57) | v2_struct_0(B_57))), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.90/1.41  tff(c_222, plain, (![B_84, C_85]: ('#skF_2'('#skF_1'(a_2_1_orders_2(B_84, C_85)), B_84, C_85)='#skF_1'(a_2_1_orders_2(B_84, C_85)) | ~m1_subset_1(C_85, k1_zfmisc_1(u1_struct_0(B_84))) | ~l1_orders_2(B_84) | ~v5_orders_2(B_84) | ~v4_orders_2(B_84) | ~v3_orders_2(B_84) | v2_struct_0(B_84) | a_2_1_orders_2(B_84, C_85)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_116])).
% 2.90/1.41  tff(c_224, plain, (![C_85]: ('#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4', C_85)), '#skF_4', C_85)='#skF_1'(a_2_1_orders_2('#skF_4', C_85)) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | a_2_1_orders_2('#skF_4', C_85)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_69, c_222])).
% 2.90/1.41  tff(c_229, plain, (![C_85]: ('#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4', C_85)), '#skF_4', C_85)='#skF_1'(a_2_1_orders_2('#skF_4', C_85)) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | a_2_1_orders_2('#skF_4', C_85)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_224])).
% 2.90/1.41  tff(c_232, plain, (![C_86]: ('#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4', C_86)), '#skF_4', C_86)='#skF_1'(a_2_1_orders_2('#skF_4', C_86)) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_struct_0('#skF_4'))) | a_2_1_orders_2('#skF_4', C_86)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_46, c_229])).
% 2.90/1.41  tff(c_235, plain, ('#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), '#skF_4', k2_struct_0('#skF_4'))='#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_47, c_232])).
% 2.90/1.41  tff(c_238, plain, ('#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), '#skF_4', k2_struct_0('#skF_4'))='#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_131, c_235])).
% 2.90/1.41  tff(c_136, plain, (![A_60, B_61, C_62]: (m1_subset_1('#skF_2'(A_60, B_61, C_62), u1_struct_0(B_61)) | ~r2_hidden(A_60, a_2_1_orders_2(B_61, C_62)) | ~m1_subset_1(C_62, k1_zfmisc_1(u1_struct_0(B_61))) | ~l1_orders_2(B_61) | ~v5_orders_2(B_61) | ~v4_orders_2(B_61) | ~v3_orders_2(B_61) | v2_struct_0(B_61))), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.90/1.41  tff(c_141, plain, (![A_60, C_62]: (m1_subset_1('#skF_2'(A_60, '#skF_4', C_62), k2_struct_0('#skF_4')) | ~r2_hidden(A_60, a_2_1_orders_2('#skF_4', C_62)) | ~m1_subset_1(C_62, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_69, c_136])).
% 2.90/1.41  tff(c_144, plain, (![A_60, C_62]: (m1_subset_1('#skF_2'(A_60, '#skF_4', C_62), k2_struct_0('#skF_4')) | ~r2_hidden(A_60, a_2_1_orders_2('#skF_4', C_62)) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_69, c_141])).
% 2.90/1.41  tff(c_145, plain, (![A_60, C_62]: (m1_subset_1('#skF_2'(A_60, '#skF_4', C_62), k2_struct_0('#skF_4')) | ~r2_hidden(A_60, a_2_1_orders_2('#skF_4', C_62)) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_46, c_144])).
% 2.90/1.41  tff(c_242, plain, (m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_238, c_145])).
% 2.90/1.41  tff(c_249, plain, (m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_47, c_242])).
% 2.90/1.41  tff(c_255, plain, (~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_249])).
% 2.90/1.41  tff(c_261, plain, (a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_255])).
% 2.90/1.41  tff(c_267, plain, $false, inference(negUnitSimplification, [status(thm)], [c_131, c_261])).
% 2.90/1.41  tff(c_268, plain, (m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_249])).
% 2.90/1.41  tff(c_8, plain, (![A_5, B_6]: (r2_hidden(A_5, B_6) | v1_xboole_0(B_6) | ~m1_subset_1(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.90/1.41  tff(c_269, plain, (r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_249])).
% 2.90/1.41  tff(c_340, plain, (![B_97, A_98, C_99, E_100]: (r2_orders_2(B_97, '#skF_2'(A_98, B_97, C_99), E_100) | ~r2_hidden(E_100, C_99) | ~m1_subset_1(E_100, u1_struct_0(B_97)) | ~r2_hidden(A_98, a_2_1_orders_2(B_97, C_99)) | ~m1_subset_1(C_99, k1_zfmisc_1(u1_struct_0(B_97))) | ~l1_orders_2(B_97) | ~v5_orders_2(B_97) | ~v4_orders_2(B_97) | ~v3_orders_2(B_97) | v2_struct_0(B_97))), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.90/1.41  tff(c_342, plain, (![A_98, C_99, E_100]: (r2_orders_2('#skF_4', '#skF_2'(A_98, '#skF_4', C_99), E_100) | ~r2_hidden(E_100, C_99) | ~m1_subset_1(E_100, u1_struct_0('#skF_4')) | ~r2_hidden(A_98, a_2_1_orders_2('#skF_4', C_99)) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_69, c_340])).
% 2.90/1.41  tff(c_347, plain, (![A_98, C_99, E_100]: (r2_orders_2('#skF_4', '#skF_2'(A_98, '#skF_4', C_99), E_100) | ~r2_hidden(E_100, C_99) | ~m1_subset_1(E_100, k2_struct_0('#skF_4')) | ~r2_hidden(A_98, a_2_1_orders_2('#skF_4', C_99)) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_69, c_342])).
% 2.90/1.41  tff(c_350, plain, (![A_101, C_102, E_103]: (r2_orders_2('#skF_4', '#skF_2'(A_101, '#skF_4', C_102), E_103) | ~r2_hidden(E_103, C_102) | ~m1_subset_1(E_103, k2_struct_0('#skF_4')) | ~r2_hidden(A_101, a_2_1_orders_2('#skF_4', C_102)) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_46, c_347])).
% 2.90/1.41  tff(c_355, plain, (![A_104, E_105]: (r2_orders_2('#skF_4', '#skF_2'(A_104, '#skF_4', k2_struct_0('#skF_4')), E_105) | ~r2_hidden(E_105, k2_struct_0('#skF_4')) | ~m1_subset_1(E_105, k2_struct_0('#skF_4')) | ~r2_hidden(A_104, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_47, c_350])).
% 2.90/1.41  tff(c_366, plain, (![E_105]: (r2_orders_2('#skF_4', '#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), E_105) | ~r2_hidden(E_105, k2_struct_0('#skF_4')) | ~m1_subset_1(E_105, k2_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_238, c_355])).
% 2.90/1.41  tff(c_379, plain, (![E_106]: (r2_orders_2('#skF_4', '#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), E_106) | ~r2_hidden(E_106, k2_struct_0('#skF_4')) | ~m1_subset_1(E_106, k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_269, c_366])).
% 2.90/1.41  tff(c_16, plain, (![A_9, C_15]: (~r2_orders_2(A_9, C_15, C_15) | ~m1_subset_1(C_15, u1_struct_0(A_9)) | ~l1_orders_2(A_9))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.90/1.41  tff(c_387, plain, (~m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_379, c_16])).
% 2.90/1.41  tff(c_397, plain, (~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_268, c_38, c_268, c_69, c_387])).
% 2.90/1.41  tff(c_414, plain, (v1_xboole_0(k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_8, c_397])).
% 2.90/1.41  tff(c_417, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_268, c_414])).
% 2.90/1.41  tff(c_419, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_417])).
% 2.90/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.41  
% 2.90/1.41  Inference rules
% 2.90/1.41  ----------------------
% 2.90/1.41  #Ref     : 0
% 2.90/1.41  #Sup     : 68
% 2.90/1.41  #Fact    : 0
% 2.90/1.41  #Define  : 0
% 2.90/1.41  #Split   : 3
% 2.90/1.41  #Chain   : 0
% 2.90/1.41  #Close   : 0
% 2.90/1.41  
% 2.90/1.41  Ordering : KBO
% 2.90/1.41  
% 2.90/1.41  Simplification rules
% 2.90/1.41  ----------------------
% 2.90/1.41  #Subsume      : 2
% 2.90/1.41  #Demod        : 151
% 2.90/1.41  #Tautology    : 24
% 2.90/1.41  #SimpNegUnit  : 23
% 2.90/1.41  #BackRed      : 1
% 2.90/1.41  
% 2.90/1.41  #Partial instantiations: 0
% 2.90/1.41  #Strategies tried      : 1
% 2.90/1.41  
% 2.90/1.41  Timing (in seconds)
% 2.90/1.41  ----------------------
% 2.90/1.41  Preprocessing        : 0.33
% 2.90/1.41  Parsing              : 0.17
% 2.90/1.41  CNF conversion       : 0.02
% 2.90/1.41  Main loop            : 0.30
% 2.90/1.41  Inferencing          : 0.11
% 2.90/1.41  Reduction            : 0.10
% 2.90/1.41  Demodulation         : 0.07
% 2.90/1.41  BG Simplification    : 0.02
% 2.90/1.41  Subsumption          : 0.05
% 2.90/1.41  Abstraction          : 0.02
% 2.90/1.41  MUC search           : 0.00
% 2.90/1.41  Cooper               : 0.00
% 2.90/1.41  Total                : 0.67
% 2.90/1.41  Index Insertion      : 0.00
% 2.90/1.41  Index Deletion       : 0.00
% 2.90/1.41  Index Matching       : 0.00
% 2.90/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
