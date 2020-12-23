%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:31 EST 2020

% Result     : Theorem 3.31s
% Output     : CNFRefutation 3.65s
% Verified   : 
% Statistics : Number of formulae       :   97 (1136 expanded)
%              Number of leaves         :   34 ( 410 expanded)
%              Depth                    :   20
%              Number of atoms          :  245 (3202 expanded)
%              Number of equality atoms :   34 ( 596 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    5 (   2 average)

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

tff(f_131,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => k2_orders_2(A,k2_struct_0(A)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_orders_2)).

tff(f_90,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_43,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_55,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_orders_2)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).

tff(c_36,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_20,plain,(
    ! [A_18] :
      ( l1_struct_0(A_18)
      | ~ l1_orders_2(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_47,plain,(
    ! [A_34] :
      ( u1_struct_0(A_34) = k2_struct_0(A_34)
      | ~ l1_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_53,plain,(
    ! [A_36] :
      ( u1_struct_0(A_36) = k2_struct_0(A_36)
      | ~ l1_orders_2(A_36) ) ),
    inference(resolution,[status(thm)],[c_20,c_47])).

tff(c_57,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_53])).

tff(c_10,plain,(
    ! [A_7] :
      ( ~ v1_xboole_0(u1_struct_0(A_7))
      | ~ l1_struct_0(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_61,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_10])).

tff(c_64,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_61])).

tff(c_66,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_69,plain,(
    ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_66])).

tff(c_73,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_69])).

tff(c_74,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_75,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_82,plain,(
    ! [A_39] :
      ( m1_subset_1(k2_struct_0(A_39),k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ l1_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_85,plain,
    ( m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ l1_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_82])).

tff(c_87,plain,(
    m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_85])).

tff(c_42,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_40,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_38,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_96,plain,(
    ! [A_50,B_51] :
      ( k2_orders_2(A_50,B_51) = a_2_1_orders_2(A_50,B_51)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ l1_orders_2(A_50)
      | ~ v5_orders_2(A_50)
      | ~ v4_orders_2(A_50)
      | ~ v3_orders_2(A_50)
      | v2_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_102,plain,(
    ! [B_51] :
      ( k2_orders_2('#skF_4',B_51) = a_2_1_orders_2('#skF_4',B_51)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_96])).

tff(c_105,plain,(
    ! [B_51] :
      ( k2_orders_2('#skF_4',B_51) = a_2_1_orders_2('#skF_4',B_51)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_102])).

tff(c_107,plain,(
    ! [B_52] :
      ( k2_orders_2('#skF_4',B_52) = a_2_1_orders_2('#skF_4',B_52)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_105])).

tff(c_111,plain,(
    k2_orders_2('#skF_4',k2_struct_0('#skF_4')) = a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_87,c_107])).

tff(c_34,plain,(
    k2_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_121,plain,(
    a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_34])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_112,plain,(
    ! [A_53,B_54,C_55] :
      ( '#skF_2'(A_53,B_54,C_55) = A_53
      | ~ r2_hidden(A_53,a_2_1_orders_2(B_54,C_55))
      | ~ m1_subset_1(C_55,k1_zfmisc_1(u1_struct_0(B_54)))
      | ~ l1_orders_2(B_54)
      | ~ v5_orders_2(B_54)
      | ~ v4_orders_2(B_54)
      | ~ v3_orders_2(B_54)
      | v2_struct_0(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_196,plain,(
    ! [B_78,C_79] :
      ( '#skF_2'('#skF_1'(a_2_1_orders_2(B_78,C_79)),B_78,C_79) = '#skF_1'(a_2_1_orders_2(B_78,C_79))
      | ~ m1_subset_1(C_79,k1_zfmisc_1(u1_struct_0(B_78)))
      | ~ l1_orders_2(B_78)
      | ~ v5_orders_2(B_78)
      | ~ v4_orders_2(B_78)
      | ~ v3_orders_2(B_78)
      | v2_struct_0(B_78)
      | a_2_1_orders_2(B_78,C_79) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_112])).

tff(c_200,plain,(
    ! [C_79] :
      ( '#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4',C_79)),'#skF_4',C_79) = '#skF_1'(a_2_1_orders_2('#skF_4',C_79))
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | a_2_1_orders_2('#skF_4',C_79) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_196])).

tff(c_203,plain,(
    ! [C_79] :
      ( '#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4',C_79)),'#skF_4',C_79) = '#skF_1'(a_2_1_orders_2('#skF_4',C_79))
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | a_2_1_orders_2('#skF_4',C_79) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_200])).

tff(c_205,plain,(
    ! [C_80] :
      ( '#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4',C_80)),'#skF_4',C_80) = '#skF_1'(a_2_1_orders_2('#skF_4',C_80))
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | a_2_1_orders_2('#skF_4',C_80) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_203])).

tff(c_207,plain,
    ( '#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),'#skF_4',k2_struct_0('#skF_4')) = '#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
    | a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_87,c_205])).

tff(c_210,plain,(
    '#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),'#skF_4',k2_struct_0('#skF_4')) = '#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_207])).

tff(c_149,plain,(
    ! [A_57,B_58,C_59] :
      ( m1_subset_1('#skF_2'(A_57,B_58,C_59),u1_struct_0(B_58))
      | ~ r2_hidden(A_57,a_2_1_orders_2(B_58,C_59))
      | ~ m1_subset_1(C_59,k1_zfmisc_1(u1_struct_0(B_58)))
      | ~ l1_orders_2(B_58)
      | ~ v5_orders_2(B_58)
      | ~ v4_orders_2(B_58)
      | ~ v3_orders_2(B_58)
      | v2_struct_0(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_154,plain,(
    ! [A_57,C_59] :
      ( m1_subset_1('#skF_2'(A_57,'#skF_4',C_59),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_57,a_2_1_orders_2('#skF_4',C_59))
      | ~ m1_subset_1(C_59,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_149])).

tff(c_157,plain,(
    ! [A_57,C_59] :
      ( m1_subset_1('#skF_2'(A_57,'#skF_4',C_59),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_57,a_2_1_orders_2('#skF_4',C_59))
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_57,c_154])).

tff(c_158,plain,(
    ! [A_57,C_59] :
      ( m1_subset_1('#skF_2'(A_57,'#skF_4',C_59),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_57,a_2_1_orders_2('#skF_4',C_59))
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_157])).

tff(c_214,plain,
    ( m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4'))
    | ~ r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
    | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_158])).

tff(c_221,plain,
    ( m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4'))
    | ~ r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_214])).

tff(c_226,plain,(
    ~ r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_221])).

tff(c_232,plain,(
    a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_226])).

tff(c_238,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_232])).

tff(c_239,plain,(
    m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_240,plain,(
    r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_8,plain,(
    ! [A_6] :
      ( m1_subset_1(k2_struct_0(A_6),k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ l1_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_201,plain,(
    ! [A_6] :
      ( '#skF_2'('#skF_1'(a_2_1_orders_2(A_6,k2_struct_0(A_6))),A_6,k2_struct_0(A_6)) = '#skF_1'(a_2_1_orders_2(A_6,k2_struct_0(A_6)))
      | ~ l1_orders_2(A_6)
      | ~ v5_orders_2(A_6)
      | ~ v4_orders_2(A_6)
      | ~ v3_orders_2(A_6)
      | v2_struct_0(A_6)
      | a_2_1_orders_2(A_6,k2_struct_0(A_6)) = k1_xboole_0
      | ~ l1_struct_0(A_6) ) ),
    inference(resolution,[status(thm)],[c_8,c_196])).

tff(c_339,plain,(
    ! [B_95,A_96,C_97,E_98] :
      ( r2_orders_2(B_95,'#skF_2'(A_96,B_95,C_97),E_98)
      | ~ r2_hidden(E_98,C_97)
      | ~ m1_subset_1(E_98,u1_struct_0(B_95))
      | ~ r2_hidden(A_96,a_2_1_orders_2(B_95,C_97))
      | ~ m1_subset_1(C_97,k1_zfmisc_1(u1_struct_0(B_95)))
      | ~ l1_orders_2(B_95)
      | ~ v5_orders_2(B_95)
      | ~ v4_orders_2(B_95)
      | ~ v3_orders_2(B_95)
      | v2_struct_0(B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_343,plain,(
    ! [A_96,C_97,E_98] :
      ( r2_orders_2('#skF_4','#skF_2'(A_96,'#skF_4',C_97),E_98)
      | ~ r2_hidden(E_98,C_97)
      | ~ m1_subset_1(E_98,u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_96,a_2_1_orders_2('#skF_4',C_97))
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_339])).

tff(c_346,plain,(
    ! [A_96,C_97,E_98] :
      ( r2_orders_2('#skF_4','#skF_2'(A_96,'#skF_4',C_97),E_98)
      | ~ r2_hidden(E_98,C_97)
      | ~ m1_subset_1(E_98,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_96,a_2_1_orders_2('#skF_4',C_97))
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_57,c_343])).

tff(c_348,plain,(
    ! [A_99,C_100,E_101] :
      ( r2_orders_2('#skF_4','#skF_2'(A_99,'#skF_4',C_100),E_101)
      | ~ r2_hidden(E_101,C_100)
      | ~ m1_subset_1(E_101,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_99,a_2_1_orders_2('#skF_4',C_100))
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_346])).

tff(c_352,plain,(
    ! [A_102,E_103] :
      ( r2_orders_2('#skF_4','#skF_2'(A_102,'#skF_4',k2_struct_0('#skF_4')),E_103)
      | ~ r2_hidden(E_103,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_103,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_102,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_87,c_348])).

tff(c_364,plain,(
    ! [E_103] :
      ( r2_orders_2('#skF_4','#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),E_103)
      | ~ r2_hidden(E_103,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_103,k2_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0
      | ~ l1_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_352])).

tff(c_379,plain,(
    ! [E_103] :
      ( r2_orders_2('#skF_4','#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),E_103)
      | ~ r2_hidden(E_103,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_103,k2_struct_0('#skF_4'))
      | v2_struct_0('#skF_4')
      | a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_42,c_40,c_38,c_36,c_240,c_364])).

tff(c_383,plain,(
    ! [E_104] :
      ( r2_orders_2('#skF_4','#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),E_104)
      | ~ r2_hidden(E_104,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_104,k2_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_44,c_379])).

tff(c_14,plain,(
    ! [A_8,C_14] :
      ( ~ r2_orders_2(A_8,C_14,C_14)
      | ~ m1_subset_1(C_14,u1_struct_0(A_8))
      | ~ l1_orders_2(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_391,plain,
    ( ~ m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4')
    | ~ r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_383,c_14])).

tff(c_401,plain,(
    ~ r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_36,c_239,c_57,c_391])).

tff(c_426,plain,
    ( v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_4,c_401])).

tff(c_429,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_426])).

tff(c_431,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_429])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:12:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.31/2.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.31/2.25  
% 3.31/2.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/2.27  %$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3
% 3.53/2.27  
% 3.53/2.27  %Foreground sorts:
% 3.53/2.27  
% 3.53/2.27  
% 3.53/2.27  %Background operators:
% 3.53/2.27  
% 3.53/2.27  
% 3.53/2.27  %Foreground operators:
% 3.53/2.27  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.53/2.27  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.53/2.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.53/2.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.53/2.27  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.53/2.27  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.53/2.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.53/2.27  tff(a_2_1_orders_2, type, a_2_1_orders_2: ($i * $i) > $i).
% 3.53/2.27  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 3.53/2.27  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.53/2.27  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.53/2.27  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.53/2.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.53/2.27  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.53/2.27  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.53/2.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.53/2.27  tff('#skF_4', type, '#skF_4': $i).
% 3.53/2.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.53/2.27  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 3.53/2.27  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.53/2.27  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.53/2.27  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.53/2.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.53/2.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.53/2.27  
% 3.65/2.33  tff(f_131, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k2_orders_2(A, k2_struct_0(A)) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_orders_2)).
% 3.65/2.33  tff(f_90, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 3.65/2.33  tff(f_43, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.65/2.33  tff(f_55, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.65/2.33  tff(f_47, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 3.65/2.33  tff(f_86, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_orders_2(A, B) = a_2_1_orders_2(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_orders_2)).
% 3.65/2.33  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.65/2.33  tff(f_117, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_1_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, D, E))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_1_orders_2)).
% 3.65/2.33  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.65/2.33  tff(f_70, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_orders_2)).
% 3.65/2.33  tff(c_36, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.65/2.33  tff(c_20, plain, (![A_18]: (l1_struct_0(A_18) | ~l1_orders_2(A_18))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.65/2.33  tff(c_44, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.65/2.33  tff(c_47, plain, (![A_34]: (u1_struct_0(A_34)=k2_struct_0(A_34) | ~l1_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.65/2.33  tff(c_53, plain, (![A_36]: (u1_struct_0(A_36)=k2_struct_0(A_36) | ~l1_orders_2(A_36))), inference(resolution, [status(thm)], [c_20, c_47])).
% 3.65/2.33  tff(c_57, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_36, c_53])).
% 3.65/2.33  tff(c_10, plain, (![A_7]: (~v1_xboole_0(u1_struct_0(A_7)) | ~l1_struct_0(A_7) | v2_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.65/2.33  tff(c_61, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_57, c_10])).
% 3.65/2.33  tff(c_64, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_44, c_61])).
% 3.65/2.33  tff(c_66, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_64])).
% 3.65/2.33  tff(c_69, plain, (~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_20, c_66])).
% 3.65/2.33  tff(c_73, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_69])).
% 3.65/2.33  tff(c_74, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_64])).
% 3.65/2.33  tff(c_75, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_64])).
% 3.65/2.33  tff(c_82, plain, (![A_39]: (m1_subset_1(k2_struct_0(A_39), k1_zfmisc_1(u1_struct_0(A_39))) | ~l1_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.65/2.33  tff(c_85, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_57, c_82])).
% 3.65/2.33  tff(c_87, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_85])).
% 3.65/2.33  tff(c_42, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.65/2.33  tff(c_40, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.65/2.33  tff(c_38, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.65/2.33  tff(c_96, plain, (![A_50, B_51]: (k2_orders_2(A_50, B_51)=a_2_1_orders_2(A_50, B_51) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_50))) | ~l1_orders_2(A_50) | ~v5_orders_2(A_50) | ~v4_orders_2(A_50) | ~v3_orders_2(A_50) | v2_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.65/2.33  tff(c_102, plain, (![B_51]: (k2_orders_2('#skF_4', B_51)=a_2_1_orders_2('#skF_4', B_51) | ~m1_subset_1(B_51, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_57, c_96])).
% 3.65/2.33  tff(c_105, plain, (![B_51]: (k2_orders_2('#skF_4', B_51)=a_2_1_orders_2('#skF_4', B_51) | ~m1_subset_1(B_51, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_102])).
% 3.65/2.33  tff(c_107, plain, (![B_52]: (k2_orders_2('#skF_4', B_52)=a_2_1_orders_2('#skF_4', B_52) | ~m1_subset_1(B_52, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_44, c_105])).
% 3.65/2.33  tff(c_111, plain, (k2_orders_2('#skF_4', k2_struct_0('#skF_4'))=a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_87, c_107])).
% 3.65/2.33  tff(c_34, plain, (k2_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.65/2.33  tff(c_121, plain, (a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_111, c_34])).
% 3.65/2.33  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.65/2.33  tff(c_112, plain, (![A_53, B_54, C_55]: ('#skF_2'(A_53, B_54, C_55)=A_53 | ~r2_hidden(A_53, a_2_1_orders_2(B_54, C_55)) | ~m1_subset_1(C_55, k1_zfmisc_1(u1_struct_0(B_54))) | ~l1_orders_2(B_54) | ~v5_orders_2(B_54) | ~v4_orders_2(B_54) | ~v3_orders_2(B_54) | v2_struct_0(B_54))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.65/2.33  tff(c_196, plain, (![B_78, C_79]: ('#skF_2'('#skF_1'(a_2_1_orders_2(B_78, C_79)), B_78, C_79)='#skF_1'(a_2_1_orders_2(B_78, C_79)) | ~m1_subset_1(C_79, k1_zfmisc_1(u1_struct_0(B_78))) | ~l1_orders_2(B_78) | ~v5_orders_2(B_78) | ~v4_orders_2(B_78) | ~v3_orders_2(B_78) | v2_struct_0(B_78) | a_2_1_orders_2(B_78, C_79)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_112])).
% 3.65/2.33  tff(c_200, plain, (![C_79]: ('#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4', C_79)), '#skF_4', C_79)='#skF_1'(a_2_1_orders_2('#skF_4', C_79)) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | a_2_1_orders_2('#skF_4', C_79)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_57, c_196])).
% 3.65/2.33  tff(c_203, plain, (![C_79]: ('#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4', C_79)), '#skF_4', C_79)='#skF_1'(a_2_1_orders_2('#skF_4', C_79)) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | a_2_1_orders_2('#skF_4', C_79)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_200])).
% 3.65/2.33  tff(c_205, plain, (![C_80]: ('#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4', C_80)), '#skF_4', C_80)='#skF_1'(a_2_1_orders_2('#skF_4', C_80)) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_struct_0('#skF_4'))) | a_2_1_orders_2('#skF_4', C_80)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_44, c_203])).
% 3.65/2.33  tff(c_207, plain, ('#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), '#skF_4', k2_struct_0('#skF_4'))='#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_87, c_205])).
% 3.65/2.33  tff(c_210, plain, ('#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), '#skF_4', k2_struct_0('#skF_4'))='#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_121, c_207])).
% 3.65/2.33  tff(c_149, plain, (![A_57, B_58, C_59]: (m1_subset_1('#skF_2'(A_57, B_58, C_59), u1_struct_0(B_58)) | ~r2_hidden(A_57, a_2_1_orders_2(B_58, C_59)) | ~m1_subset_1(C_59, k1_zfmisc_1(u1_struct_0(B_58))) | ~l1_orders_2(B_58) | ~v5_orders_2(B_58) | ~v4_orders_2(B_58) | ~v3_orders_2(B_58) | v2_struct_0(B_58))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.65/2.33  tff(c_154, plain, (![A_57, C_59]: (m1_subset_1('#skF_2'(A_57, '#skF_4', C_59), k2_struct_0('#skF_4')) | ~r2_hidden(A_57, a_2_1_orders_2('#skF_4', C_59)) | ~m1_subset_1(C_59, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_57, c_149])).
% 3.65/2.33  tff(c_157, plain, (![A_57, C_59]: (m1_subset_1('#skF_2'(A_57, '#skF_4', C_59), k2_struct_0('#skF_4')) | ~r2_hidden(A_57, a_2_1_orders_2('#skF_4', C_59)) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_57, c_154])).
% 3.65/2.33  tff(c_158, plain, (![A_57, C_59]: (m1_subset_1('#skF_2'(A_57, '#skF_4', C_59), k2_struct_0('#skF_4')) | ~r2_hidden(A_57, a_2_1_orders_2('#skF_4', C_59)) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_44, c_157])).
% 3.65/2.33  tff(c_214, plain, (m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_210, c_158])).
% 3.65/2.33  tff(c_221, plain, (m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_214])).
% 3.65/2.33  tff(c_226, plain, (~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_221])).
% 3.65/2.33  tff(c_232, plain, (a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_226])).
% 3.65/2.33  tff(c_238, plain, $false, inference(negUnitSimplification, [status(thm)], [c_121, c_232])).
% 3.65/2.33  tff(c_239, plain, (m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_221])).
% 3.65/2.33  tff(c_4, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.65/2.33  tff(c_240, plain, (r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_221])).
% 3.65/2.33  tff(c_8, plain, (![A_6]: (m1_subset_1(k2_struct_0(A_6), k1_zfmisc_1(u1_struct_0(A_6))) | ~l1_struct_0(A_6))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.65/2.33  tff(c_201, plain, (![A_6]: ('#skF_2'('#skF_1'(a_2_1_orders_2(A_6, k2_struct_0(A_6))), A_6, k2_struct_0(A_6))='#skF_1'(a_2_1_orders_2(A_6, k2_struct_0(A_6))) | ~l1_orders_2(A_6) | ~v5_orders_2(A_6) | ~v4_orders_2(A_6) | ~v3_orders_2(A_6) | v2_struct_0(A_6) | a_2_1_orders_2(A_6, k2_struct_0(A_6))=k1_xboole_0 | ~l1_struct_0(A_6))), inference(resolution, [status(thm)], [c_8, c_196])).
% 3.65/2.33  tff(c_339, plain, (![B_95, A_96, C_97, E_98]: (r2_orders_2(B_95, '#skF_2'(A_96, B_95, C_97), E_98) | ~r2_hidden(E_98, C_97) | ~m1_subset_1(E_98, u1_struct_0(B_95)) | ~r2_hidden(A_96, a_2_1_orders_2(B_95, C_97)) | ~m1_subset_1(C_97, k1_zfmisc_1(u1_struct_0(B_95))) | ~l1_orders_2(B_95) | ~v5_orders_2(B_95) | ~v4_orders_2(B_95) | ~v3_orders_2(B_95) | v2_struct_0(B_95))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.65/2.33  tff(c_343, plain, (![A_96, C_97, E_98]: (r2_orders_2('#skF_4', '#skF_2'(A_96, '#skF_4', C_97), E_98) | ~r2_hidden(E_98, C_97) | ~m1_subset_1(E_98, u1_struct_0('#skF_4')) | ~r2_hidden(A_96, a_2_1_orders_2('#skF_4', C_97)) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_57, c_339])).
% 3.65/2.33  tff(c_346, plain, (![A_96, C_97, E_98]: (r2_orders_2('#skF_4', '#skF_2'(A_96, '#skF_4', C_97), E_98) | ~r2_hidden(E_98, C_97) | ~m1_subset_1(E_98, k2_struct_0('#skF_4')) | ~r2_hidden(A_96, a_2_1_orders_2('#skF_4', C_97)) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_57, c_343])).
% 3.65/2.33  tff(c_348, plain, (![A_99, C_100, E_101]: (r2_orders_2('#skF_4', '#skF_2'(A_99, '#skF_4', C_100), E_101) | ~r2_hidden(E_101, C_100) | ~m1_subset_1(E_101, k2_struct_0('#skF_4')) | ~r2_hidden(A_99, a_2_1_orders_2('#skF_4', C_100)) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_44, c_346])).
% 3.65/2.33  tff(c_352, plain, (![A_102, E_103]: (r2_orders_2('#skF_4', '#skF_2'(A_102, '#skF_4', k2_struct_0('#skF_4')), E_103) | ~r2_hidden(E_103, k2_struct_0('#skF_4')) | ~m1_subset_1(E_103, k2_struct_0('#skF_4')) | ~r2_hidden(A_102, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_87, c_348])).
% 3.65/2.33  tff(c_364, plain, (![E_103]: (r2_orders_2('#skF_4', '#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), E_103) | ~r2_hidden(E_103, k2_struct_0('#skF_4')) | ~m1_subset_1(E_103, k2_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0 | ~l1_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_201, c_352])).
% 3.65/2.33  tff(c_379, plain, (![E_103]: (r2_orders_2('#skF_4', '#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), E_103) | ~r2_hidden(E_103, k2_struct_0('#skF_4')) | ~m1_subset_1(E_103, k2_struct_0('#skF_4')) | v2_struct_0('#skF_4') | a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_75, c_42, c_40, c_38, c_36, c_240, c_364])).
% 3.65/2.33  tff(c_383, plain, (![E_104]: (r2_orders_2('#skF_4', '#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), E_104) | ~r2_hidden(E_104, k2_struct_0('#skF_4')) | ~m1_subset_1(E_104, k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_121, c_44, c_379])).
% 3.65/2.33  tff(c_14, plain, (![A_8, C_14]: (~r2_orders_2(A_8, C_14, C_14) | ~m1_subset_1(C_14, u1_struct_0(A_8)) | ~l1_orders_2(A_8))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.65/2.33  tff(c_391, plain, (~m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_383, c_14])).
% 3.65/2.33  tff(c_401, plain, (~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_239, c_36, c_239, c_57, c_391])).
% 3.65/2.33  tff(c_426, plain, (v1_xboole_0(k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_4, c_401])).
% 3.65/2.33  tff(c_429, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_239, c_426])).
% 3.65/2.33  tff(c_431, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_429])).
% 3.65/2.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.65/2.33  
% 3.65/2.33  Inference rules
% 3.65/2.33  ----------------------
% 3.65/2.33  #Ref     : 0
% 3.65/2.33  #Sup     : 71
% 3.65/2.33  #Fact    : 0
% 3.65/2.33  #Define  : 0
% 3.65/2.33  #Split   : 3
% 3.65/2.33  #Chain   : 0
% 3.65/2.33  #Close   : 0
% 3.65/2.33  
% 3.65/2.33  Ordering : KBO
% 3.65/2.33  
% 3.65/2.33  Simplification rules
% 3.65/2.33  ----------------------
% 3.65/2.33  #Subsume      : 2
% 3.65/2.33  #Demod        : 155
% 3.65/2.33  #Tautology    : 25
% 3.65/2.33  #SimpNegUnit  : 24
% 3.65/2.33  #BackRed      : 1
% 3.65/2.33  
% 3.65/2.33  #Partial instantiations: 0
% 3.65/2.33  #Strategies tried      : 1
% 3.65/2.33  
% 3.65/2.33  Timing (in seconds)
% 3.65/2.33  ----------------------
% 3.65/2.33  Preprocessing        : 0.61
% 3.65/2.33  Parsing              : 0.32
% 3.65/2.33  CNF conversion       : 0.04
% 3.65/2.33  Main loop            : 0.70
% 3.65/2.33  Inferencing          : 0.29
% 3.65/2.33  Reduction            : 0.20
% 3.65/2.33  Demodulation         : 0.13
% 3.65/2.33  BG Simplification    : 0.04
% 3.74/2.35  Subsumption          : 0.13
% 3.74/2.35  Abstraction          : 0.05
% 3.74/2.35  MUC search           : 0.00
% 3.74/2.35  Cooper               : 0.00
% 3.74/2.35  Total                : 1.43
% 3.74/2.35  Index Insertion      : 0.00
% 3.74/2.35  Index Deletion       : 0.00
% 3.74/2.35  Index Matching       : 0.00
% 3.74/2.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
