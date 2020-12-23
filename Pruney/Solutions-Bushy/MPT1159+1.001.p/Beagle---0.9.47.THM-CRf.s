%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1159+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:31 EST 2020

% Result     : Theorem 4.29s
% Output     : CNFRefutation 4.62s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 174 expanded)
%              Number of leaves         :   29 (  80 expanded)
%              Depth                    :   12
%              Number of atoms          :  216 ( 779 expanded)
%              Number of equality atoms :   21 (  27 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k9_subset_1 > k3_orders_2 > k6_domain_1 > k3_xboole_0 > k2_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_orders_2,type,(
    k3_orders_2: ( $i * $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_orders_2,type,(
    k2_orders_2: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_104,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                   => ( r2_hidden(B,k3_orders_2(A,D,C))
                    <=> ( r2_orders_2(A,B,C)
                        & r2_hidden(B,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).

tff(f_77,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_orders_2(A,B,C)
              <=> r2_hidden(B,k2_orders_2(A,k6_domain_1(u1_struct_0(A),C))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_orders_2)).

tff(f_43,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => k3_orders_2(A,B,C) = k9_subset_1(u1_struct_0(A),k2_orders_2(A,k6_domain_1(u1_struct_0(A),C)),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_orders_2)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_32,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_54,plain,
    ( r2_hidden('#skF_4',k3_orders_2('#skF_3','#skF_6','#skF_5'))
    | r2_orders_2('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_58,plain,(
    r2_orders_2('#skF_3','#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_50,plain,
    ( r2_hidden('#skF_4',k3_orders_2('#skF_3','#skF_6','#skF_5'))
    | r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_56,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_40,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_38,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_36,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_34,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_26,plain,(
    ! [B_21,A_17,C_23] :
      ( r2_hidden(B_21,k2_orders_2(A_17,k6_domain_1(u1_struct_0(A_17),C_23)))
      | ~ r2_orders_2(A_17,B_21,C_23)
      | ~ m1_subset_1(C_23,u1_struct_0(A_17))
      | ~ m1_subset_1(B_21,u1_struct_0(A_17))
      | ~ l1_orders_2(A_17)
      | ~ v5_orders_2(A_17)
      | ~ v4_orders_2(A_17)
      | ~ v3_orders_2(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_28,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_658,plain,(
    ! [A_109,C_110,B_111] :
      ( k9_subset_1(u1_struct_0(A_109),k2_orders_2(A_109,k6_domain_1(u1_struct_0(A_109),C_110)),B_111) = k3_orders_2(A_109,B_111,C_110)
      | ~ m1_subset_1(C_110,u1_struct_0(A_109))
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ l1_orders_2(A_109)
      | ~ v5_orders_2(A_109)
      | ~ v4_orders_2(A_109)
      | ~ v3_orders_2(A_109)
      | v2_struct_0(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_68,plain,(
    ! [A_44,B_45,C_46] :
      ( k9_subset_1(A_44,B_45,C_46) = k3_xboole_0(B_45,C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(A_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_71,plain,(
    ! [B_45] : k9_subset_1(u1_struct_0('#skF_3'),B_45,'#skF_6') = k3_xboole_0(B_45,'#skF_6') ),
    inference(resolution,[status(thm)],[c_28,c_68])).

tff(c_665,plain,(
    ! [C_110] :
      ( k3_xboole_0(k2_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_110)),'#skF_6') = k3_orders_2('#skF_3','#skF_6',C_110)
      | ~ m1_subset_1(C_110,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_658,c_71])).

tff(c_675,plain,(
    ! [C_110] :
      ( k3_xboole_0(k2_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_110)),'#skF_6') = k3_orders_2('#skF_3','#skF_6',C_110)
      | ~ m1_subset_1(C_110,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_28,c_665])).

tff(c_705,plain,(
    ! [C_115] :
      ( k3_xboole_0(k2_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_115)),'#skF_6') = k3_orders_2('#skF_3','#skF_6',C_115)
      | ~ m1_subset_1(C_115,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_675])).

tff(c_4,plain,(
    ! [D_13,A_8,B_9] :
      ( r2_hidden(D_13,k3_xboole_0(A_8,B_9))
      | ~ r2_hidden(D_13,B_9)
      | ~ r2_hidden(D_13,A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_998,plain,(
    ! [D_122,C_123] :
      ( r2_hidden(D_122,k3_orders_2('#skF_3','#skF_6',C_123))
      | ~ r2_hidden(D_122,'#skF_6')
      | ~ r2_hidden(D_122,k2_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_123)))
      | ~ m1_subset_1(C_123,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_705,c_4])).

tff(c_1037,plain,(
    ! [B_21,C_23] :
      ( r2_hidden(B_21,k3_orders_2('#skF_3','#skF_6',C_23))
      | ~ r2_hidden(B_21,'#skF_6')
      | ~ r2_orders_2('#skF_3',B_21,C_23)
      | ~ m1_subset_1(C_23,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_21,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26,c_998])).

tff(c_1097,plain,(
    ! [B_21,C_23] :
      ( r2_hidden(B_21,k3_orders_2('#skF_3','#skF_6',C_23))
      | ~ r2_hidden(B_21,'#skF_6')
      | ~ r2_orders_2('#skF_3',B_21,C_23)
      | ~ m1_subset_1(C_23,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_21,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_1037])).

tff(c_1111,plain,(
    ! [B_124,C_125] :
      ( r2_hidden(B_124,k3_orders_2('#skF_3','#skF_6',C_125))
      | ~ r2_hidden(B_124,'#skF_6')
      | ~ r2_orders_2('#skF_3',B_124,C_125)
      | ~ m1_subset_1(C_125,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_124,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_1097])).

tff(c_44,plain,
    ( ~ r2_hidden('#skF_4','#skF_6')
    | ~ r2_orders_2('#skF_3','#skF_4','#skF_5')
    | ~ r2_hidden('#skF_4',k3_orders_2('#skF_3','#skF_6','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_82,plain,(
    ~ r2_hidden('#skF_4',k3_orders_2('#skF_3','#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_44])).

tff(c_1133,plain,
    ( ~ r2_hidden('#skF_4','#skF_6')
    | ~ r2_orders_2('#skF_3','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1111,c_82])).

tff(c_1143,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_58,c_56,c_1133])).

tff(c_1145,plain,(
    ~ r2_orders_2('#skF_3','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_1144,plain,(
    r2_hidden('#skF_4',k3_orders_2('#skF_3','#skF_6','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_1874,plain,(
    ! [A_205,C_206,B_207] :
      ( k9_subset_1(u1_struct_0(A_205),k2_orders_2(A_205,k6_domain_1(u1_struct_0(A_205),C_206)),B_207) = k3_orders_2(A_205,B_207,C_206)
      | ~ m1_subset_1(C_206,u1_struct_0(A_205))
      | ~ m1_subset_1(B_207,k1_zfmisc_1(u1_struct_0(A_205)))
      | ~ l1_orders_2(A_205)
      | ~ v5_orders_2(A_205)
      | ~ v4_orders_2(A_205)
      | ~ v3_orders_2(A_205)
      | v2_struct_0(A_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1155,plain,(
    ! [A_129,B_130,C_131] :
      ( k9_subset_1(A_129,B_130,C_131) = k3_xboole_0(B_130,C_131)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(A_129)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1158,plain,(
    ! [B_130] : k9_subset_1(u1_struct_0('#skF_3'),B_130,'#skF_6') = k3_xboole_0(B_130,'#skF_6') ),
    inference(resolution,[status(thm)],[c_28,c_1155])).

tff(c_1881,plain,(
    ! [C_206] :
      ( k3_xboole_0(k2_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_206)),'#skF_6') = k3_orders_2('#skF_3','#skF_6',C_206)
      | ~ m1_subset_1(C_206,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1874,c_1158])).

tff(c_1891,plain,(
    ! [C_206] :
      ( k3_xboole_0(k2_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_206)),'#skF_6') = k3_orders_2('#skF_3','#skF_6',C_206)
      | ~ m1_subset_1(C_206,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_28,c_1881])).

tff(c_1897,plain,(
    ! [C_208] :
      ( k3_xboole_0(k2_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_208)),'#skF_6') = k3_orders_2('#skF_3','#skF_6',C_208)
      | ~ m1_subset_1(C_208,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_1891])).

tff(c_8,plain,(
    ! [D_13,A_8,B_9] :
      ( r2_hidden(D_13,A_8)
      | ~ r2_hidden(D_13,k3_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2100,plain,(
    ! [D_211,C_212] :
      ( r2_hidden(D_211,k2_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_212)))
      | ~ r2_hidden(D_211,k3_orders_2('#skF_3','#skF_6',C_212))
      | ~ m1_subset_1(C_212,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1897,c_8])).

tff(c_24,plain,(
    ! [A_17,B_21,C_23] :
      ( r2_orders_2(A_17,B_21,C_23)
      | ~ r2_hidden(B_21,k2_orders_2(A_17,k6_domain_1(u1_struct_0(A_17),C_23)))
      | ~ m1_subset_1(C_23,u1_struct_0(A_17))
      | ~ m1_subset_1(B_21,u1_struct_0(A_17))
      | ~ l1_orders_2(A_17)
      | ~ v5_orders_2(A_17)
      | ~ v4_orders_2(A_17)
      | ~ v3_orders_2(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2103,plain,(
    ! [D_211,C_212] :
      ( r2_orders_2('#skF_3',D_211,C_212)
      | ~ m1_subset_1(D_211,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r2_hidden(D_211,k3_orders_2('#skF_3','#skF_6',C_212))
      | ~ m1_subset_1(C_212,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_2100,c_24])).

tff(c_2119,plain,(
    ! [D_211,C_212] :
      ( r2_orders_2('#skF_3',D_211,C_212)
      | ~ m1_subset_1(D_211,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3')
      | ~ r2_hidden(D_211,k3_orders_2('#skF_3','#skF_6',C_212))
      | ~ m1_subset_1(C_212,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_2103])).

tff(c_2125,plain,(
    ! [D_213,C_214] :
      ( r2_orders_2('#skF_3',D_213,C_214)
      | ~ m1_subset_1(D_213,u1_struct_0('#skF_3'))
      | ~ r2_hidden(D_213,k3_orders_2('#skF_3','#skF_6',C_214))
      | ~ m1_subset_1(C_214,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_2119])).

tff(c_2224,plain,
    ( r2_orders_2('#skF_3','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1144,c_2125])).

tff(c_2251,plain,(
    r2_orders_2('#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32,c_2224])).

tff(c_2253,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1145,c_2251])).

tff(c_2255,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_2254,plain,(
    r2_hidden('#skF_4',k3_orders_2('#skF_3','#skF_6','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_2853,plain,(
    ! [A_286,C_287,B_288] :
      ( k9_subset_1(u1_struct_0(A_286),k2_orders_2(A_286,k6_domain_1(u1_struct_0(A_286),C_287)),B_288) = k3_orders_2(A_286,B_288,C_287)
      | ~ m1_subset_1(C_287,u1_struct_0(A_286))
      | ~ m1_subset_1(B_288,k1_zfmisc_1(u1_struct_0(A_286)))
      | ~ l1_orders_2(A_286)
      | ~ v5_orders_2(A_286)
      | ~ v4_orders_2(A_286)
      | ~ v3_orders_2(A_286)
      | v2_struct_0(A_286) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2269,plain,(
    ! [A_221,B_222,C_223] :
      ( k9_subset_1(A_221,B_222,C_223) = k3_xboole_0(B_222,C_223)
      | ~ m1_subset_1(C_223,k1_zfmisc_1(A_221)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2272,plain,(
    ! [B_222] : k9_subset_1(u1_struct_0('#skF_3'),B_222,'#skF_6') = k3_xboole_0(B_222,'#skF_6') ),
    inference(resolution,[status(thm)],[c_28,c_2269])).

tff(c_2860,plain,(
    ! [C_287] :
      ( k3_xboole_0(k2_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_287)),'#skF_6') = k3_orders_2('#skF_3','#skF_6',C_287)
      | ~ m1_subset_1(C_287,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2853,c_2272])).

tff(c_2870,plain,(
    ! [C_287] :
      ( k3_xboole_0(k2_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_287)),'#skF_6') = k3_orders_2('#skF_3','#skF_6',C_287)
      | ~ m1_subset_1(C_287,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_28,c_2860])).

tff(c_2876,plain,(
    ! [C_289] :
      ( k3_xboole_0(k2_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_289)),'#skF_6') = k3_orders_2('#skF_3','#skF_6',C_289)
      | ~ m1_subset_1(C_289,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_2870])).

tff(c_6,plain,(
    ! [D_13,B_9,A_8] :
      ( r2_hidden(D_13,B_9)
      | ~ r2_hidden(D_13,k3_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2935,plain,(
    ! [D_290,C_291] :
      ( r2_hidden(D_290,'#skF_6')
      | ~ r2_hidden(D_290,k3_orders_2('#skF_3','#skF_6',C_291))
      | ~ m1_subset_1(C_291,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2876,c_6])).

tff(c_3014,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2254,c_2935])).

tff(c_3036,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_3014])).

tff(c_3038,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2255,c_3036])).

%------------------------------------------------------------------------------
