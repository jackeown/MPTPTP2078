%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:31 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :   98 (1137 expanded)
%              Number of leaves         :   35 ( 411 expanded)
%              Depth                    :   20
%              Number of atoms          :  248 (3223 expanded)
%              Number of equality atoms :   35 ( 603 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k4_mcart_1 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3

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

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_139,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => k2_orders_2(A,k2_struct_0(A)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_orders_2)).

tff(f_98,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_63,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_94,axiom,(
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

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_mcart_1(C,D,E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).

tff(f_125,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_78,axiom,(
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

tff(c_40,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_24,plain,(
    ! [A_34] :
      ( l1_struct_0(A_34)
      | ~ l1_orders_2(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_51,plain,(
    ! [A_50] :
      ( u1_struct_0(A_50) = k2_struct_0(A_50)
      | ~ l1_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_57,plain,(
    ! [A_52] :
      ( u1_struct_0(A_52) = k2_struct_0(A_52)
      | ~ l1_orders_2(A_52) ) ),
    inference(resolution,[status(thm)],[c_24,c_51])).

tff(c_61,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_57])).

tff(c_14,plain,(
    ! [A_23] :
      ( ~ v1_xboole_0(u1_struct_0(A_23))
      | ~ l1_struct_0(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_65,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_14])).

tff(c_68,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_65])).

tff(c_70,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_73,plain,(
    ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_70])).

tff(c_77,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_73])).

tff(c_78,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_79,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_85,plain,(
    ! [A_53] :
      ( m1_subset_1(k2_struct_0(A_53),k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_88,plain,
    ( m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ l1_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_85])).

tff(c_90,plain,(
    m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_88])).

tff(c_46,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_44,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_42,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_118,plain,(
    ! [A_94,B_95] :
      ( k2_orders_2(A_94,B_95) = a_2_1_orders_2(A_94,B_95)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_orders_2(A_94)
      | ~ v5_orders_2(A_94)
      | ~ v4_orders_2(A_94)
      | ~ v3_orders_2(A_94)
      | v2_struct_0(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_124,plain,(
    ! [B_95] :
      ( k2_orders_2('#skF_4',B_95) = a_2_1_orders_2('#skF_4',B_95)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_118])).

tff(c_127,plain,(
    ! [B_95] :
      ( k2_orders_2('#skF_4',B_95) = a_2_1_orders_2('#skF_4',B_95)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_124])).

tff(c_129,plain,(
    ! [B_96] :
      ( k2_orders_2('#skF_4',B_96) = a_2_1_orders_2('#skF_4',B_96)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_127])).

tff(c_133,plain,(
    k2_orders_2('#skF_4',k2_struct_0('#skF_4')) = a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_90,c_129])).

tff(c_38,plain,(
    k2_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_134,plain,(
    a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_38])).

tff(c_4,plain,(
    ! [A_3] :
      ( r2_hidden('#skF_1'(A_3),A_3)
      | k1_xboole_0 = A_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_162,plain,(
    ! [A_98,B_99,C_100] :
      ( '#skF_2'(A_98,B_99,C_100) = A_98
      | ~ r2_hidden(A_98,a_2_1_orders_2(B_99,C_100))
      | ~ m1_subset_1(C_100,k1_zfmisc_1(u1_struct_0(B_99)))
      | ~ l1_orders_2(B_99)
      | ~ v5_orders_2(B_99)
      | ~ v4_orders_2(B_99)
      | ~ v3_orders_2(B_99)
      | v2_struct_0(B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_200,plain,(
    ! [B_113,C_114] :
      ( '#skF_2'('#skF_1'(a_2_1_orders_2(B_113,C_114)),B_113,C_114) = '#skF_1'(a_2_1_orders_2(B_113,C_114))
      | ~ m1_subset_1(C_114,k1_zfmisc_1(u1_struct_0(B_113)))
      | ~ l1_orders_2(B_113)
      | ~ v5_orders_2(B_113)
      | ~ v4_orders_2(B_113)
      | ~ v3_orders_2(B_113)
      | v2_struct_0(B_113)
      | a_2_1_orders_2(B_113,C_114) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_162])).

tff(c_204,plain,(
    ! [C_114] :
      ( '#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4',C_114)),'#skF_4',C_114) = '#skF_1'(a_2_1_orders_2('#skF_4',C_114))
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | a_2_1_orders_2('#skF_4',C_114) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_200])).

tff(c_207,plain,(
    ! [C_114] :
      ( '#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4',C_114)),'#skF_4',C_114) = '#skF_1'(a_2_1_orders_2('#skF_4',C_114))
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | a_2_1_orders_2('#skF_4',C_114) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_204])).

tff(c_209,plain,(
    ! [C_115] :
      ( '#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4',C_115)),'#skF_4',C_115) = '#skF_1'(a_2_1_orders_2('#skF_4',C_115))
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | a_2_1_orders_2('#skF_4',C_115) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_207])).

tff(c_211,plain,
    ( '#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),'#skF_4',k2_struct_0('#skF_4')) = '#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
    | a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_90,c_209])).

tff(c_214,plain,(
    '#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),'#skF_4',k2_struct_0('#skF_4')) = '#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_211])).

tff(c_171,plain,(
    ! [A_101,B_102,C_103] :
      ( m1_subset_1('#skF_2'(A_101,B_102,C_103),u1_struct_0(B_102))
      | ~ r2_hidden(A_101,a_2_1_orders_2(B_102,C_103))
      | ~ m1_subset_1(C_103,k1_zfmisc_1(u1_struct_0(B_102)))
      | ~ l1_orders_2(B_102)
      | ~ v5_orders_2(B_102)
      | ~ v4_orders_2(B_102)
      | ~ v3_orders_2(B_102)
      | v2_struct_0(B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_176,plain,(
    ! [A_101,C_103] :
      ( m1_subset_1('#skF_2'(A_101,'#skF_4',C_103),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_101,a_2_1_orders_2('#skF_4',C_103))
      | ~ m1_subset_1(C_103,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_171])).

tff(c_179,plain,(
    ! [A_101,C_103] :
      ( m1_subset_1('#skF_2'(A_101,'#skF_4',C_103),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_101,a_2_1_orders_2('#skF_4',C_103))
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_61,c_176])).

tff(c_180,plain,(
    ! [A_101,C_103] :
      ( m1_subset_1('#skF_2'(A_101,'#skF_4',C_103),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_101,a_2_1_orders_2('#skF_4',C_103))
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_179])).

tff(c_218,plain,
    ( m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4'))
    | ~ r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
    | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_180])).

tff(c_225,plain,
    ( m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4'))
    | ~ r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_218])).

tff(c_239,plain,(
    ~ r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_225])).

tff(c_245,plain,(
    a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_239])).

tff(c_251,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_245])).

tff(c_252,plain,(
    m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_225])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_253,plain,(
    r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_225])).

tff(c_12,plain,(
    ! [A_22] :
      ( m1_subset_1(k2_struct_0(A_22),k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ l1_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_205,plain,(
    ! [A_22] :
      ( '#skF_2'('#skF_1'(a_2_1_orders_2(A_22,k2_struct_0(A_22))),A_22,k2_struct_0(A_22)) = '#skF_1'(a_2_1_orders_2(A_22,k2_struct_0(A_22)))
      | ~ l1_orders_2(A_22)
      | ~ v5_orders_2(A_22)
      | ~ v4_orders_2(A_22)
      | ~ v3_orders_2(A_22)
      | v2_struct_0(A_22)
      | a_2_1_orders_2(A_22,k2_struct_0(A_22)) = k1_xboole_0
      | ~ l1_struct_0(A_22) ) ),
    inference(resolution,[status(thm)],[c_12,c_200])).

tff(c_740,plain,(
    ! [B_188,A_189,C_190,E_191] :
      ( r2_orders_2(B_188,'#skF_2'(A_189,B_188,C_190),E_191)
      | ~ r2_hidden(E_191,C_190)
      | ~ m1_subset_1(E_191,u1_struct_0(B_188))
      | ~ r2_hidden(A_189,a_2_1_orders_2(B_188,C_190))
      | ~ m1_subset_1(C_190,k1_zfmisc_1(u1_struct_0(B_188)))
      | ~ l1_orders_2(B_188)
      | ~ v5_orders_2(B_188)
      | ~ v4_orders_2(B_188)
      | ~ v3_orders_2(B_188)
      | v2_struct_0(B_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_744,plain,(
    ! [A_189,C_190,E_191] :
      ( r2_orders_2('#skF_4','#skF_2'(A_189,'#skF_4',C_190),E_191)
      | ~ r2_hidden(E_191,C_190)
      | ~ m1_subset_1(E_191,u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_189,a_2_1_orders_2('#skF_4',C_190))
      | ~ m1_subset_1(C_190,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_740])).

tff(c_747,plain,(
    ! [A_189,C_190,E_191] :
      ( r2_orders_2('#skF_4','#skF_2'(A_189,'#skF_4',C_190),E_191)
      | ~ r2_hidden(E_191,C_190)
      | ~ m1_subset_1(E_191,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_189,a_2_1_orders_2('#skF_4',C_190))
      | ~ m1_subset_1(C_190,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_61,c_744])).

tff(c_749,plain,(
    ! [A_192,C_193,E_194] :
      ( r2_orders_2('#skF_4','#skF_2'(A_192,'#skF_4',C_193),E_194)
      | ~ r2_hidden(E_194,C_193)
      | ~ m1_subset_1(E_194,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_192,a_2_1_orders_2('#skF_4',C_193))
      | ~ m1_subset_1(C_193,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_747])).

tff(c_753,plain,(
    ! [A_195,E_196] :
      ( r2_orders_2('#skF_4','#skF_2'(A_195,'#skF_4',k2_struct_0('#skF_4')),E_196)
      | ~ r2_hidden(E_196,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_196,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_195,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_90,c_749])).

tff(c_765,plain,(
    ! [E_196] :
      ( r2_orders_2('#skF_4','#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),E_196)
      | ~ r2_hidden(E_196,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_196,k2_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0
      | ~ l1_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_753])).

tff(c_780,plain,(
    ! [E_196] :
      ( r2_orders_2('#skF_4','#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),E_196)
      | ~ r2_hidden(E_196,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_196,k2_struct_0('#skF_4'))
      | v2_struct_0('#skF_4')
      | a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_46,c_44,c_42,c_40,c_253,c_765])).

tff(c_784,plain,(
    ! [E_197] :
      ( r2_orders_2('#skF_4','#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),E_197)
      | ~ r2_hidden(E_197,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_197,k2_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_48,c_780])).

tff(c_18,plain,(
    ! [A_24,C_30] :
      ( ~ r2_orders_2(A_24,C_30,C_30)
      | ~ m1_subset_1(C_30,u1_struct_0(A_24))
      | ~ l1_orders_2(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_792,plain,
    ( ~ m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4')
    | ~ r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_784,c_18])).

tff(c_802,plain,(
    ~ r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_40,c_252,c_61,c_792])).

tff(c_805,plain,
    ( v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_2,c_802])).

tff(c_808,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_805])).

tff(c_810,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_808])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:17:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.23/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.49  
% 3.23/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.49  %$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k4_mcart_1 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3
% 3.23/1.49  
% 3.23/1.49  %Foreground sorts:
% 3.23/1.49  
% 3.23/1.49  
% 3.23/1.49  %Background operators:
% 3.23/1.49  
% 3.23/1.49  
% 3.23/1.49  %Foreground operators:
% 3.23/1.49  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.23/1.49  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.23/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.23/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.23/1.49  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.23/1.49  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.23/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.23/1.49  tff(a_2_1_orders_2, type, a_2_1_orders_2: ($i * $i) > $i).
% 3.23/1.49  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 3.23/1.49  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.23/1.49  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.23/1.49  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.23/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.23/1.49  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.23/1.49  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.23/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.23/1.49  tff('#skF_4', type, '#skF_4': $i).
% 3.23/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.23/1.49  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 3.23/1.49  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.23/1.49  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.23/1.49  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 3.23/1.49  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.23/1.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.23/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.23/1.49  
% 3.23/1.51  tff(f_139, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k2_orders_2(A, k2_struct_0(A)) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_orders_2)).
% 3.23/1.51  tff(f_98, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 3.23/1.51  tff(f_51, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.23/1.51  tff(f_63, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.23/1.51  tff(f_55, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 3.23/1.51  tff(f_94, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_orders_2(A, B) = a_2_1_orders_2(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_orders_2)).
% 3.23/1.51  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_mcart_1(C, D, E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_mcart_1)).
% 3.23/1.51  tff(f_125, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_1_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, D, E))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_1_orders_2)).
% 3.23/1.51  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.23/1.51  tff(f_78, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_orders_2)).
% 3.23/1.51  tff(c_40, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.23/1.51  tff(c_24, plain, (![A_34]: (l1_struct_0(A_34) | ~l1_orders_2(A_34))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.23/1.51  tff(c_48, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.23/1.51  tff(c_51, plain, (![A_50]: (u1_struct_0(A_50)=k2_struct_0(A_50) | ~l1_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.23/1.51  tff(c_57, plain, (![A_52]: (u1_struct_0(A_52)=k2_struct_0(A_52) | ~l1_orders_2(A_52))), inference(resolution, [status(thm)], [c_24, c_51])).
% 3.23/1.51  tff(c_61, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_40, c_57])).
% 3.23/1.51  tff(c_14, plain, (![A_23]: (~v1_xboole_0(u1_struct_0(A_23)) | ~l1_struct_0(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.23/1.51  tff(c_65, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_61, c_14])).
% 3.23/1.51  tff(c_68, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_48, c_65])).
% 3.23/1.51  tff(c_70, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_68])).
% 3.23/1.51  tff(c_73, plain, (~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_24, c_70])).
% 3.23/1.51  tff(c_77, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_73])).
% 3.23/1.51  tff(c_78, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_68])).
% 3.23/1.51  tff(c_79, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_68])).
% 3.23/1.51  tff(c_85, plain, (![A_53]: (m1_subset_1(k2_struct_0(A_53), k1_zfmisc_1(u1_struct_0(A_53))) | ~l1_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.23/1.51  tff(c_88, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_61, c_85])).
% 3.23/1.51  tff(c_90, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_88])).
% 3.23/1.51  tff(c_46, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.23/1.51  tff(c_44, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.23/1.51  tff(c_42, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.23/1.51  tff(c_118, plain, (![A_94, B_95]: (k2_orders_2(A_94, B_95)=a_2_1_orders_2(A_94, B_95) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_orders_2(A_94) | ~v5_orders_2(A_94) | ~v4_orders_2(A_94) | ~v3_orders_2(A_94) | v2_struct_0(A_94))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.23/1.51  tff(c_124, plain, (![B_95]: (k2_orders_2('#skF_4', B_95)=a_2_1_orders_2('#skF_4', B_95) | ~m1_subset_1(B_95, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_61, c_118])).
% 3.23/1.51  tff(c_127, plain, (![B_95]: (k2_orders_2('#skF_4', B_95)=a_2_1_orders_2('#skF_4', B_95) | ~m1_subset_1(B_95, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_124])).
% 3.23/1.51  tff(c_129, plain, (![B_96]: (k2_orders_2('#skF_4', B_96)=a_2_1_orders_2('#skF_4', B_96) | ~m1_subset_1(B_96, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_48, c_127])).
% 3.23/1.51  tff(c_133, plain, (k2_orders_2('#skF_4', k2_struct_0('#skF_4'))=a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_90, c_129])).
% 3.23/1.51  tff(c_38, plain, (k2_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.23/1.51  tff(c_134, plain, (a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_133, c_38])).
% 3.23/1.51  tff(c_4, plain, (![A_3]: (r2_hidden('#skF_1'(A_3), A_3) | k1_xboole_0=A_3)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.23/1.51  tff(c_162, plain, (![A_98, B_99, C_100]: ('#skF_2'(A_98, B_99, C_100)=A_98 | ~r2_hidden(A_98, a_2_1_orders_2(B_99, C_100)) | ~m1_subset_1(C_100, k1_zfmisc_1(u1_struct_0(B_99))) | ~l1_orders_2(B_99) | ~v5_orders_2(B_99) | ~v4_orders_2(B_99) | ~v3_orders_2(B_99) | v2_struct_0(B_99))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.23/1.51  tff(c_200, plain, (![B_113, C_114]: ('#skF_2'('#skF_1'(a_2_1_orders_2(B_113, C_114)), B_113, C_114)='#skF_1'(a_2_1_orders_2(B_113, C_114)) | ~m1_subset_1(C_114, k1_zfmisc_1(u1_struct_0(B_113))) | ~l1_orders_2(B_113) | ~v5_orders_2(B_113) | ~v4_orders_2(B_113) | ~v3_orders_2(B_113) | v2_struct_0(B_113) | a_2_1_orders_2(B_113, C_114)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_162])).
% 3.23/1.51  tff(c_204, plain, (![C_114]: ('#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4', C_114)), '#skF_4', C_114)='#skF_1'(a_2_1_orders_2('#skF_4', C_114)) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | a_2_1_orders_2('#skF_4', C_114)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_61, c_200])).
% 3.23/1.51  tff(c_207, plain, (![C_114]: ('#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4', C_114)), '#skF_4', C_114)='#skF_1'(a_2_1_orders_2('#skF_4', C_114)) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | a_2_1_orders_2('#skF_4', C_114)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_204])).
% 3.23/1.51  tff(c_209, plain, (![C_115]: ('#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4', C_115)), '#skF_4', C_115)='#skF_1'(a_2_1_orders_2('#skF_4', C_115)) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_struct_0('#skF_4'))) | a_2_1_orders_2('#skF_4', C_115)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_48, c_207])).
% 3.23/1.51  tff(c_211, plain, ('#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), '#skF_4', k2_struct_0('#skF_4'))='#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_90, c_209])).
% 3.23/1.51  tff(c_214, plain, ('#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), '#skF_4', k2_struct_0('#skF_4'))='#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_134, c_211])).
% 3.23/1.51  tff(c_171, plain, (![A_101, B_102, C_103]: (m1_subset_1('#skF_2'(A_101, B_102, C_103), u1_struct_0(B_102)) | ~r2_hidden(A_101, a_2_1_orders_2(B_102, C_103)) | ~m1_subset_1(C_103, k1_zfmisc_1(u1_struct_0(B_102))) | ~l1_orders_2(B_102) | ~v5_orders_2(B_102) | ~v4_orders_2(B_102) | ~v3_orders_2(B_102) | v2_struct_0(B_102))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.23/1.51  tff(c_176, plain, (![A_101, C_103]: (m1_subset_1('#skF_2'(A_101, '#skF_4', C_103), k2_struct_0('#skF_4')) | ~r2_hidden(A_101, a_2_1_orders_2('#skF_4', C_103)) | ~m1_subset_1(C_103, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_61, c_171])).
% 3.23/1.51  tff(c_179, plain, (![A_101, C_103]: (m1_subset_1('#skF_2'(A_101, '#skF_4', C_103), k2_struct_0('#skF_4')) | ~r2_hidden(A_101, a_2_1_orders_2('#skF_4', C_103)) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_61, c_176])).
% 3.23/1.51  tff(c_180, plain, (![A_101, C_103]: (m1_subset_1('#skF_2'(A_101, '#skF_4', C_103), k2_struct_0('#skF_4')) | ~r2_hidden(A_101, a_2_1_orders_2('#skF_4', C_103)) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_48, c_179])).
% 3.23/1.51  tff(c_218, plain, (m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_214, c_180])).
% 3.23/1.51  tff(c_225, plain, (m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_218])).
% 3.23/1.51  tff(c_239, plain, (~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_225])).
% 3.23/1.51  tff(c_245, plain, (a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_239])).
% 3.23/1.51  tff(c_251, plain, $false, inference(negUnitSimplification, [status(thm)], [c_134, c_245])).
% 3.23/1.51  tff(c_252, plain, (m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_225])).
% 3.23/1.51  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.23/1.51  tff(c_253, plain, (r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_225])).
% 3.23/1.51  tff(c_12, plain, (![A_22]: (m1_subset_1(k2_struct_0(A_22), k1_zfmisc_1(u1_struct_0(A_22))) | ~l1_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.23/1.51  tff(c_205, plain, (![A_22]: ('#skF_2'('#skF_1'(a_2_1_orders_2(A_22, k2_struct_0(A_22))), A_22, k2_struct_0(A_22))='#skF_1'(a_2_1_orders_2(A_22, k2_struct_0(A_22))) | ~l1_orders_2(A_22) | ~v5_orders_2(A_22) | ~v4_orders_2(A_22) | ~v3_orders_2(A_22) | v2_struct_0(A_22) | a_2_1_orders_2(A_22, k2_struct_0(A_22))=k1_xboole_0 | ~l1_struct_0(A_22))), inference(resolution, [status(thm)], [c_12, c_200])).
% 3.23/1.51  tff(c_740, plain, (![B_188, A_189, C_190, E_191]: (r2_orders_2(B_188, '#skF_2'(A_189, B_188, C_190), E_191) | ~r2_hidden(E_191, C_190) | ~m1_subset_1(E_191, u1_struct_0(B_188)) | ~r2_hidden(A_189, a_2_1_orders_2(B_188, C_190)) | ~m1_subset_1(C_190, k1_zfmisc_1(u1_struct_0(B_188))) | ~l1_orders_2(B_188) | ~v5_orders_2(B_188) | ~v4_orders_2(B_188) | ~v3_orders_2(B_188) | v2_struct_0(B_188))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.23/1.51  tff(c_744, plain, (![A_189, C_190, E_191]: (r2_orders_2('#skF_4', '#skF_2'(A_189, '#skF_4', C_190), E_191) | ~r2_hidden(E_191, C_190) | ~m1_subset_1(E_191, u1_struct_0('#skF_4')) | ~r2_hidden(A_189, a_2_1_orders_2('#skF_4', C_190)) | ~m1_subset_1(C_190, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_61, c_740])).
% 3.23/1.51  tff(c_747, plain, (![A_189, C_190, E_191]: (r2_orders_2('#skF_4', '#skF_2'(A_189, '#skF_4', C_190), E_191) | ~r2_hidden(E_191, C_190) | ~m1_subset_1(E_191, k2_struct_0('#skF_4')) | ~r2_hidden(A_189, a_2_1_orders_2('#skF_4', C_190)) | ~m1_subset_1(C_190, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_61, c_744])).
% 3.23/1.51  tff(c_749, plain, (![A_192, C_193, E_194]: (r2_orders_2('#skF_4', '#skF_2'(A_192, '#skF_4', C_193), E_194) | ~r2_hidden(E_194, C_193) | ~m1_subset_1(E_194, k2_struct_0('#skF_4')) | ~r2_hidden(A_192, a_2_1_orders_2('#skF_4', C_193)) | ~m1_subset_1(C_193, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_48, c_747])).
% 3.23/1.51  tff(c_753, plain, (![A_195, E_196]: (r2_orders_2('#skF_4', '#skF_2'(A_195, '#skF_4', k2_struct_0('#skF_4')), E_196) | ~r2_hidden(E_196, k2_struct_0('#skF_4')) | ~m1_subset_1(E_196, k2_struct_0('#skF_4')) | ~r2_hidden(A_195, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_90, c_749])).
% 3.23/1.51  tff(c_765, plain, (![E_196]: (r2_orders_2('#skF_4', '#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), E_196) | ~r2_hidden(E_196, k2_struct_0('#skF_4')) | ~m1_subset_1(E_196, k2_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0 | ~l1_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_205, c_753])).
% 3.23/1.51  tff(c_780, plain, (![E_196]: (r2_orders_2('#skF_4', '#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), E_196) | ~r2_hidden(E_196, k2_struct_0('#skF_4')) | ~m1_subset_1(E_196, k2_struct_0('#skF_4')) | v2_struct_0('#skF_4') | a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_79, c_46, c_44, c_42, c_40, c_253, c_765])).
% 3.23/1.51  tff(c_784, plain, (![E_197]: (r2_orders_2('#skF_4', '#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), E_197) | ~r2_hidden(E_197, k2_struct_0('#skF_4')) | ~m1_subset_1(E_197, k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_134, c_48, c_780])).
% 3.23/1.51  tff(c_18, plain, (![A_24, C_30]: (~r2_orders_2(A_24, C_30, C_30) | ~m1_subset_1(C_30, u1_struct_0(A_24)) | ~l1_orders_2(A_24))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.23/1.51  tff(c_792, plain, (~m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_784, c_18])).
% 3.23/1.51  tff(c_802, plain, (~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_252, c_40, c_252, c_61, c_792])).
% 3.23/1.51  tff(c_805, plain, (v1_xboole_0(k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_2, c_802])).
% 3.23/1.51  tff(c_808, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_252, c_805])).
% 3.23/1.51  tff(c_810, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_808])).
% 3.23/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.51  
% 3.23/1.51  Inference rules
% 3.23/1.51  ----------------------
% 3.23/1.51  #Ref     : 0
% 3.23/1.51  #Sup     : 145
% 3.23/1.51  #Fact    : 0
% 3.23/1.51  #Define  : 0
% 3.23/1.51  #Split   : 4
% 3.23/1.51  #Chain   : 0
% 3.23/1.51  #Close   : 0
% 3.23/1.51  
% 3.23/1.51  Ordering : KBO
% 3.23/1.51  
% 3.23/1.51  Simplification rules
% 3.23/1.51  ----------------------
% 3.23/1.51  #Subsume      : 13
% 3.23/1.51  #Demod        : 335
% 3.23/1.51  #Tautology    : 50
% 3.23/1.51  #SimpNegUnit  : 51
% 3.23/1.51  #BackRed      : 19
% 3.23/1.51  
% 3.23/1.51  #Partial instantiations: 0
% 3.23/1.51  #Strategies tried      : 1
% 3.23/1.51  
% 3.23/1.51  Timing (in seconds)
% 3.23/1.51  ----------------------
% 3.23/1.51  Preprocessing        : 0.33
% 3.23/1.51  Parsing              : 0.18
% 3.23/1.51  CNF conversion       : 0.02
% 3.23/1.51  Main loop            : 0.40
% 3.23/1.51  Inferencing          : 0.15
% 3.23/1.51  Reduction            : 0.13
% 3.23/1.52  Demodulation         : 0.08
% 3.23/1.52  BG Simplification    : 0.02
% 3.23/1.52  Subsumption          : 0.07
% 3.23/1.52  Abstraction          : 0.03
% 3.23/1.52  MUC search           : 0.00
% 3.23/1.52  Cooper               : 0.00
% 3.23/1.52  Total                : 0.77
% 3.23/1.52  Index Insertion      : 0.00
% 3.23/1.52  Index Deletion       : 0.00
% 3.23/1.52  Index Matching       : 0.00
% 3.23/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
