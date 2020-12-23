%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:31 EST 2020

% Result     : Theorem 3.63s
% Output     : CNFRefutation 3.63s
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
%$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k3_mcart_1 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_orders_2)).

tff(f_98,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_63,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_orders_2)).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).

tff(c_40,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_24,plain,(
    ! [A_30] :
      ( l1_struct_0(A_30)
      | ~ l1_orders_2(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_51,plain,(
    ! [A_46] :
      ( u1_struct_0(A_46) = k2_struct_0(A_46)
      | ~ l1_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_57,plain,(
    ! [A_48] :
      ( u1_struct_0(A_48) = k2_struct_0(A_48)
      | ~ l1_orders_2(A_48) ) ),
    inference(resolution,[status(thm)],[c_24,c_51])).

tff(c_61,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_57])).

tff(c_14,plain,(
    ! [A_19] :
      ( ~ v1_xboole_0(u1_struct_0(A_19))
      | ~ l1_struct_0(A_19)
      | v2_struct_0(A_19) ) ),
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
    ! [A_49] :
      ( m1_subset_1(k2_struct_0(A_49),k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ l1_struct_0(A_49) ) ),
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
    ! [A_84,B_85] :
      ( k2_orders_2(A_84,B_85) = a_2_1_orders_2(A_84,B_85)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_orders_2(A_84)
      | ~ v5_orders_2(A_84)
      | ~ v4_orders_2(A_84)
      | ~ v3_orders_2(A_84)
      | v2_struct_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_124,plain,(
    ! [B_85] :
      ( k2_orders_2('#skF_4',B_85) = a_2_1_orders_2('#skF_4',B_85)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_118])).

tff(c_127,plain,(
    ! [B_85] :
      ( k2_orders_2('#skF_4',B_85) = a_2_1_orders_2('#skF_4',B_85)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_124])).

tff(c_129,plain,(
    ! [B_86] :
      ( k2_orders_2('#skF_4',B_86) = a_2_1_orders_2('#skF_4',B_86)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
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
    ! [A_88,B_89,C_90] :
      ( '#skF_2'(A_88,B_89,C_90) = A_88
      | ~ r2_hidden(A_88,a_2_1_orders_2(B_89,C_90))
      | ~ m1_subset_1(C_90,k1_zfmisc_1(u1_struct_0(B_89)))
      | ~ l1_orders_2(B_89)
      | ~ v5_orders_2(B_89)
      | ~ v4_orders_2(B_89)
      | ~ v3_orders_2(B_89)
      | v2_struct_0(B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_200,plain,(
    ! [B_103,C_104] :
      ( '#skF_2'('#skF_1'(a_2_1_orders_2(B_103,C_104)),B_103,C_104) = '#skF_1'(a_2_1_orders_2(B_103,C_104))
      | ~ m1_subset_1(C_104,k1_zfmisc_1(u1_struct_0(B_103)))
      | ~ l1_orders_2(B_103)
      | ~ v5_orders_2(B_103)
      | ~ v4_orders_2(B_103)
      | ~ v3_orders_2(B_103)
      | v2_struct_0(B_103)
      | a_2_1_orders_2(B_103,C_104) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_162])).

tff(c_204,plain,(
    ! [C_104] :
      ( '#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4',C_104)),'#skF_4',C_104) = '#skF_1'(a_2_1_orders_2('#skF_4',C_104))
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | a_2_1_orders_2('#skF_4',C_104) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_200])).

tff(c_207,plain,(
    ! [C_104] :
      ( '#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4',C_104)),'#skF_4',C_104) = '#skF_1'(a_2_1_orders_2('#skF_4',C_104))
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | a_2_1_orders_2('#skF_4',C_104) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_204])).

tff(c_209,plain,(
    ! [C_105] :
      ( '#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4',C_105)),'#skF_4',C_105) = '#skF_1'(a_2_1_orders_2('#skF_4',C_105))
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | a_2_1_orders_2('#skF_4',C_105) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_207])).

tff(c_211,plain,
    ( '#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),'#skF_4',k2_struct_0('#skF_4')) = '#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
    | a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_90,c_209])).

tff(c_214,plain,(
    '#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),'#skF_4',k2_struct_0('#skF_4')) = '#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_211])).

tff(c_171,plain,(
    ! [A_91,B_92,C_93] :
      ( m1_subset_1('#skF_2'(A_91,B_92,C_93),u1_struct_0(B_92))
      | ~ r2_hidden(A_91,a_2_1_orders_2(B_92,C_93))
      | ~ m1_subset_1(C_93,k1_zfmisc_1(u1_struct_0(B_92)))
      | ~ l1_orders_2(B_92)
      | ~ v5_orders_2(B_92)
      | ~ v4_orders_2(B_92)
      | ~ v3_orders_2(B_92)
      | v2_struct_0(B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_176,plain,(
    ! [A_91,C_93] :
      ( m1_subset_1('#skF_2'(A_91,'#skF_4',C_93),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_91,a_2_1_orders_2('#skF_4',C_93))
      | ~ m1_subset_1(C_93,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_171])).

tff(c_179,plain,(
    ! [A_91,C_93] :
      ( m1_subset_1('#skF_2'(A_91,'#skF_4',C_93),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_91,a_2_1_orders_2('#skF_4',C_93))
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_61,c_176])).

tff(c_180,plain,(
    ! [A_91,C_93] :
      ( m1_subset_1('#skF_2'(A_91,'#skF_4',C_93),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_91,a_2_1_orders_2('#skF_4',C_93))
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
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
    ! [A_18] :
      ( m1_subset_1(k2_struct_0(A_18),k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_205,plain,(
    ! [A_18] :
      ( '#skF_2'('#skF_1'(a_2_1_orders_2(A_18,k2_struct_0(A_18))),A_18,k2_struct_0(A_18)) = '#skF_1'(a_2_1_orders_2(A_18,k2_struct_0(A_18)))
      | ~ l1_orders_2(A_18)
      | ~ v5_orders_2(A_18)
      | ~ v4_orders_2(A_18)
      | ~ v3_orders_2(A_18)
      | v2_struct_0(A_18)
      | a_2_1_orders_2(A_18,k2_struct_0(A_18)) = k1_xboole_0
      | ~ l1_struct_0(A_18) ) ),
    inference(resolution,[status(thm)],[c_12,c_200])).

tff(c_740,plain,(
    ! [B_172,A_173,C_174,E_175] :
      ( r2_orders_2(B_172,'#skF_2'(A_173,B_172,C_174),E_175)
      | ~ r2_hidden(E_175,C_174)
      | ~ m1_subset_1(E_175,u1_struct_0(B_172))
      | ~ r2_hidden(A_173,a_2_1_orders_2(B_172,C_174))
      | ~ m1_subset_1(C_174,k1_zfmisc_1(u1_struct_0(B_172)))
      | ~ l1_orders_2(B_172)
      | ~ v5_orders_2(B_172)
      | ~ v4_orders_2(B_172)
      | ~ v3_orders_2(B_172)
      | v2_struct_0(B_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_744,plain,(
    ! [A_173,C_174,E_175] :
      ( r2_orders_2('#skF_4','#skF_2'(A_173,'#skF_4',C_174),E_175)
      | ~ r2_hidden(E_175,C_174)
      | ~ m1_subset_1(E_175,u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_173,a_2_1_orders_2('#skF_4',C_174))
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_740])).

tff(c_747,plain,(
    ! [A_173,C_174,E_175] :
      ( r2_orders_2('#skF_4','#skF_2'(A_173,'#skF_4',C_174),E_175)
      | ~ r2_hidden(E_175,C_174)
      | ~ m1_subset_1(E_175,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_173,a_2_1_orders_2('#skF_4',C_174))
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_61,c_744])).

tff(c_749,plain,(
    ! [A_176,C_177,E_178] :
      ( r2_orders_2('#skF_4','#skF_2'(A_176,'#skF_4',C_177),E_178)
      | ~ r2_hidden(E_178,C_177)
      | ~ m1_subset_1(E_178,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_176,a_2_1_orders_2('#skF_4',C_177))
      | ~ m1_subset_1(C_177,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_747])).

tff(c_753,plain,(
    ! [A_179,E_180] :
      ( r2_orders_2('#skF_4','#skF_2'(A_179,'#skF_4',k2_struct_0('#skF_4')),E_180)
      | ~ r2_hidden(E_180,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_180,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_179,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_90,c_749])).

tff(c_765,plain,(
    ! [E_180] :
      ( r2_orders_2('#skF_4','#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),E_180)
      | ~ r2_hidden(E_180,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_180,k2_struct_0('#skF_4'))
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
    ! [E_180] :
      ( r2_orders_2('#skF_4','#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),E_180)
      | ~ r2_hidden(E_180,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_180,k2_struct_0('#skF_4'))
      | v2_struct_0('#skF_4')
      | a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_46,c_44,c_42,c_40,c_253,c_765])).

tff(c_784,plain,(
    ! [E_181] :
      ( r2_orders_2('#skF_4','#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),E_181)
      | ~ r2_hidden(E_181,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_181,k2_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_48,c_780])).

tff(c_18,plain,(
    ! [A_20,C_26] :
      ( ~ r2_orders_2(A_20,C_26,C_26)
      | ~ m1_subset_1(C_26,u1_struct_0(A_20))
      | ~ l1_orders_2(A_20) ) ),
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
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:25:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.63/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.63/1.59  
% 3.63/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.63/1.59  %$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k3_mcart_1 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3
% 3.63/1.59  
% 3.63/1.59  %Foreground sorts:
% 3.63/1.59  
% 3.63/1.59  
% 3.63/1.59  %Background operators:
% 3.63/1.59  
% 3.63/1.59  
% 3.63/1.59  %Foreground operators:
% 3.63/1.59  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.63/1.59  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.63/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.63/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.63/1.59  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.63/1.59  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.63/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.63/1.59  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 3.63/1.59  tff(a_2_1_orders_2, type, a_2_1_orders_2: ($i * $i) > $i).
% 3.63/1.59  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 3.63/1.59  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.63/1.59  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.63/1.59  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.63/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.63/1.59  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.63/1.59  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.63/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.63/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.63/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.63/1.59  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 3.63/1.59  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.63/1.59  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.63/1.59  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.63/1.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.63/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.63/1.59  
% 3.63/1.61  tff(f_139, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k2_orders_2(A, k2_struct_0(A)) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_orders_2)).
% 3.63/1.61  tff(f_98, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 3.63/1.61  tff(f_51, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.63/1.61  tff(f_63, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.63/1.61  tff(f_55, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 3.63/1.61  tff(f_94, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_orders_2(A, B) = a_2_1_orders_2(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_orders_2)).
% 3.63/1.61  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_mcart_1)).
% 3.63/1.61  tff(f_125, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_1_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, D, E))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_1_orders_2)).
% 3.63/1.61  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.63/1.61  tff(f_78, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_orders_2)).
% 3.63/1.61  tff(c_40, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.63/1.61  tff(c_24, plain, (![A_30]: (l1_struct_0(A_30) | ~l1_orders_2(A_30))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.63/1.61  tff(c_48, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.63/1.61  tff(c_51, plain, (![A_46]: (u1_struct_0(A_46)=k2_struct_0(A_46) | ~l1_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.63/1.61  tff(c_57, plain, (![A_48]: (u1_struct_0(A_48)=k2_struct_0(A_48) | ~l1_orders_2(A_48))), inference(resolution, [status(thm)], [c_24, c_51])).
% 3.63/1.61  tff(c_61, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_40, c_57])).
% 3.63/1.61  tff(c_14, plain, (![A_19]: (~v1_xboole_0(u1_struct_0(A_19)) | ~l1_struct_0(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.63/1.61  tff(c_65, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_61, c_14])).
% 3.63/1.61  tff(c_68, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_48, c_65])).
% 3.63/1.61  tff(c_70, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_68])).
% 3.63/1.61  tff(c_73, plain, (~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_24, c_70])).
% 3.63/1.61  tff(c_77, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_73])).
% 3.63/1.61  tff(c_78, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_68])).
% 3.63/1.61  tff(c_79, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_68])).
% 3.63/1.61  tff(c_85, plain, (![A_49]: (m1_subset_1(k2_struct_0(A_49), k1_zfmisc_1(u1_struct_0(A_49))) | ~l1_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.63/1.61  tff(c_88, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_61, c_85])).
% 3.63/1.61  tff(c_90, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_88])).
% 3.63/1.61  tff(c_46, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.63/1.61  tff(c_44, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.63/1.61  tff(c_42, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.63/1.61  tff(c_118, plain, (![A_84, B_85]: (k2_orders_2(A_84, B_85)=a_2_1_orders_2(A_84, B_85) | ~m1_subset_1(B_85, k1_zfmisc_1(u1_struct_0(A_84))) | ~l1_orders_2(A_84) | ~v5_orders_2(A_84) | ~v4_orders_2(A_84) | ~v3_orders_2(A_84) | v2_struct_0(A_84))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.63/1.61  tff(c_124, plain, (![B_85]: (k2_orders_2('#skF_4', B_85)=a_2_1_orders_2('#skF_4', B_85) | ~m1_subset_1(B_85, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_61, c_118])).
% 3.63/1.61  tff(c_127, plain, (![B_85]: (k2_orders_2('#skF_4', B_85)=a_2_1_orders_2('#skF_4', B_85) | ~m1_subset_1(B_85, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_124])).
% 3.63/1.61  tff(c_129, plain, (![B_86]: (k2_orders_2('#skF_4', B_86)=a_2_1_orders_2('#skF_4', B_86) | ~m1_subset_1(B_86, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_48, c_127])).
% 3.63/1.61  tff(c_133, plain, (k2_orders_2('#skF_4', k2_struct_0('#skF_4'))=a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_90, c_129])).
% 3.63/1.61  tff(c_38, plain, (k2_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.63/1.61  tff(c_134, plain, (a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_133, c_38])).
% 3.63/1.61  tff(c_4, plain, (![A_3]: (r2_hidden('#skF_1'(A_3), A_3) | k1_xboole_0=A_3)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.63/1.61  tff(c_162, plain, (![A_88, B_89, C_90]: ('#skF_2'(A_88, B_89, C_90)=A_88 | ~r2_hidden(A_88, a_2_1_orders_2(B_89, C_90)) | ~m1_subset_1(C_90, k1_zfmisc_1(u1_struct_0(B_89))) | ~l1_orders_2(B_89) | ~v5_orders_2(B_89) | ~v4_orders_2(B_89) | ~v3_orders_2(B_89) | v2_struct_0(B_89))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.63/1.61  tff(c_200, plain, (![B_103, C_104]: ('#skF_2'('#skF_1'(a_2_1_orders_2(B_103, C_104)), B_103, C_104)='#skF_1'(a_2_1_orders_2(B_103, C_104)) | ~m1_subset_1(C_104, k1_zfmisc_1(u1_struct_0(B_103))) | ~l1_orders_2(B_103) | ~v5_orders_2(B_103) | ~v4_orders_2(B_103) | ~v3_orders_2(B_103) | v2_struct_0(B_103) | a_2_1_orders_2(B_103, C_104)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_162])).
% 3.63/1.61  tff(c_204, plain, (![C_104]: ('#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4', C_104)), '#skF_4', C_104)='#skF_1'(a_2_1_orders_2('#skF_4', C_104)) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | a_2_1_orders_2('#skF_4', C_104)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_61, c_200])).
% 3.63/1.61  tff(c_207, plain, (![C_104]: ('#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4', C_104)), '#skF_4', C_104)='#skF_1'(a_2_1_orders_2('#skF_4', C_104)) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | a_2_1_orders_2('#skF_4', C_104)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_204])).
% 3.63/1.61  tff(c_209, plain, (![C_105]: ('#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4', C_105)), '#skF_4', C_105)='#skF_1'(a_2_1_orders_2('#skF_4', C_105)) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_struct_0('#skF_4'))) | a_2_1_orders_2('#skF_4', C_105)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_48, c_207])).
% 3.63/1.61  tff(c_211, plain, ('#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), '#skF_4', k2_struct_0('#skF_4'))='#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_90, c_209])).
% 3.63/1.61  tff(c_214, plain, ('#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), '#skF_4', k2_struct_0('#skF_4'))='#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_134, c_211])).
% 3.63/1.61  tff(c_171, plain, (![A_91, B_92, C_93]: (m1_subset_1('#skF_2'(A_91, B_92, C_93), u1_struct_0(B_92)) | ~r2_hidden(A_91, a_2_1_orders_2(B_92, C_93)) | ~m1_subset_1(C_93, k1_zfmisc_1(u1_struct_0(B_92))) | ~l1_orders_2(B_92) | ~v5_orders_2(B_92) | ~v4_orders_2(B_92) | ~v3_orders_2(B_92) | v2_struct_0(B_92))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.63/1.61  tff(c_176, plain, (![A_91, C_93]: (m1_subset_1('#skF_2'(A_91, '#skF_4', C_93), k2_struct_0('#skF_4')) | ~r2_hidden(A_91, a_2_1_orders_2('#skF_4', C_93)) | ~m1_subset_1(C_93, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_61, c_171])).
% 3.63/1.61  tff(c_179, plain, (![A_91, C_93]: (m1_subset_1('#skF_2'(A_91, '#skF_4', C_93), k2_struct_0('#skF_4')) | ~r2_hidden(A_91, a_2_1_orders_2('#skF_4', C_93)) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_61, c_176])).
% 3.63/1.61  tff(c_180, plain, (![A_91, C_93]: (m1_subset_1('#skF_2'(A_91, '#skF_4', C_93), k2_struct_0('#skF_4')) | ~r2_hidden(A_91, a_2_1_orders_2('#skF_4', C_93)) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_48, c_179])).
% 3.63/1.61  tff(c_218, plain, (m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_214, c_180])).
% 3.63/1.61  tff(c_225, plain, (m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_218])).
% 3.63/1.61  tff(c_239, plain, (~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_225])).
% 3.63/1.61  tff(c_245, plain, (a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_239])).
% 3.63/1.61  tff(c_251, plain, $false, inference(negUnitSimplification, [status(thm)], [c_134, c_245])).
% 3.63/1.61  tff(c_252, plain, (m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_225])).
% 3.63/1.61  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.63/1.61  tff(c_253, plain, (r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_225])).
% 3.63/1.61  tff(c_12, plain, (![A_18]: (m1_subset_1(k2_struct_0(A_18), k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.63/1.61  tff(c_205, plain, (![A_18]: ('#skF_2'('#skF_1'(a_2_1_orders_2(A_18, k2_struct_0(A_18))), A_18, k2_struct_0(A_18))='#skF_1'(a_2_1_orders_2(A_18, k2_struct_0(A_18))) | ~l1_orders_2(A_18) | ~v5_orders_2(A_18) | ~v4_orders_2(A_18) | ~v3_orders_2(A_18) | v2_struct_0(A_18) | a_2_1_orders_2(A_18, k2_struct_0(A_18))=k1_xboole_0 | ~l1_struct_0(A_18))), inference(resolution, [status(thm)], [c_12, c_200])).
% 3.63/1.61  tff(c_740, plain, (![B_172, A_173, C_174, E_175]: (r2_orders_2(B_172, '#skF_2'(A_173, B_172, C_174), E_175) | ~r2_hidden(E_175, C_174) | ~m1_subset_1(E_175, u1_struct_0(B_172)) | ~r2_hidden(A_173, a_2_1_orders_2(B_172, C_174)) | ~m1_subset_1(C_174, k1_zfmisc_1(u1_struct_0(B_172))) | ~l1_orders_2(B_172) | ~v5_orders_2(B_172) | ~v4_orders_2(B_172) | ~v3_orders_2(B_172) | v2_struct_0(B_172))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.63/1.61  tff(c_744, plain, (![A_173, C_174, E_175]: (r2_orders_2('#skF_4', '#skF_2'(A_173, '#skF_4', C_174), E_175) | ~r2_hidden(E_175, C_174) | ~m1_subset_1(E_175, u1_struct_0('#skF_4')) | ~r2_hidden(A_173, a_2_1_orders_2('#skF_4', C_174)) | ~m1_subset_1(C_174, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_61, c_740])).
% 3.63/1.61  tff(c_747, plain, (![A_173, C_174, E_175]: (r2_orders_2('#skF_4', '#skF_2'(A_173, '#skF_4', C_174), E_175) | ~r2_hidden(E_175, C_174) | ~m1_subset_1(E_175, k2_struct_0('#skF_4')) | ~r2_hidden(A_173, a_2_1_orders_2('#skF_4', C_174)) | ~m1_subset_1(C_174, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_61, c_744])).
% 3.63/1.61  tff(c_749, plain, (![A_176, C_177, E_178]: (r2_orders_2('#skF_4', '#skF_2'(A_176, '#skF_4', C_177), E_178) | ~r2_hidden(E_178, C_177) | ~m1_subset_1(E_178, k2_struct_0('#skF_4')) | ~r2_hidden(A_176, a_2_1_orders_2('#skF_4', C_177)) | ~m1_subset_1(C_177, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_48, c_747])).
% 3.63/1.61  tff(c_753, plain, (![A_179, E_180]: (r2_orders_2('#skF_4', '#skF_2'(A_179, '#skF_4', k2_struct_0('#skF_4')), E_180) | ~r2_hidden(E_180, k2_struct_0('#skF_4')) | ~m1_subset_1(E_180, k2_struct_0('#skF_4')) | ~r2_hidden(A_179, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_90, c_749])).
% 3.63/1.61  tff(c_765, plain, (![E_180]: (r2_orders_2('#skF_4', '#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), E_180) | ~r2_hidden(E_180, k2_struct_0('#skF_4')) | ~m1_subset_1(E_180, k2_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0 | ~l1_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_205, c_753])).
% 3.63/1.61  tff(c_780, plain, (![E_180]: (r2_orders_2('#skF_4', '#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), E_180) | ~r2_hidden(E_180, k2_struct_0('#skF_4')) | ~m1_subset_1(E_180, k2_struct_0('#skF_4')) | v2_struct_0('#skF_4') | a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_79, c_46, c_44, c_42, c_40, c_253, c_765])).
% 3.63/1.61  tff(c_784, plain, (![E_181]: (r2_orders_2('#skF_4', '#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), E_181) | ~r2_hidden(E_181, k2_struct_0('#skF_4')) | ~m1_subset_1(E_181, k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_134, c_48, c_780])).
% 3.63/1.61  tff(c_18, plain, (![A_20, C_26]: (~r2_orders_2(A_20, C_26, C_26) | ~m1_subset_1(C_26, u1_struct_0(A_20)) | ~l1_orders_2(A_20))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.63/1.61  tff(c_792, plain, (~m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_784, c_18])).
% 3.63/1.61  tff(c_802, plain, (~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_252, c_40, c_252, c_61, c_792])).
% 3.63/1.61  tff(c_805, plain, (v1_xboole_0(k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_2, c_802])).
% 3.63/1.61  tff(c_808, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_252, c_805])).
% 3.63/1.61  tff(c_810, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_808])).
% 3.63/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.63/1.61  
% 3.63/1.61  Inference rules
% 3.63/1.61  ----------------------
% 3.63/1.61  #Ref     : 0
% 3.63/1.61  #Sup     : 145
% 3.63/1.61  #Fact    : 0
% 3.63/1.61  #Define  : 0
% 3.63/1.61  #Split   : 4
% 3.63/1.61  #Chain   : 0
% 3.63/1.61  #Close   : 0
% 3.63/1.61  
% 3.63/1.61  Ordering : KBO
% 3.63/1.61  
% 3.63/1.61  Simplification rules
% 3.63/1.61  ----------------------
% 3.63/1.61  #Subsume      : 13
% 3.63/1.61  #Demod        : 335
% 3.63/1.61  #Tautology    : 50
% 3.63/1.61  #SimpNegUnit  : 51
% 3.63/1.61  #BackRed      : 19
% 3.63/1.61  
% 3.63/1.61  #Partial instantiations: 0
% 3.63/1.61  #Strategies tried      : 1
% 3.63/1.61  
% 3.63/1.61  Timing (in seconds)
% 3.63/1.61  ----------------------
% 3.63/1.62  Preprocessing        : 0.35
% 3.63/1.62  Parsing              : 0.18
% 3.63/1.62  CNF conversion       : 0.03
% 3.63/1.62  Main loop            : 0.47
% 3.63/1.62  Inferencing          : 0.18
% 3.63/1.62  Reduction            : 0.15
% 3.63/1.62  Demodulation         : 0.10
% 3.63/1.62  BG Simplification    : 0.03
% 3.63/1.62  Subsumption          : 0.08
% 3.63/1.62  Abstraction          : 0.03
% 3.63/1.62  MUC search           : 0.00
% 3.63/1.62  Cooper               : 0.00
% 3.63/1.62  Total                : 0.87
% 3.63/1.62  Index Insertion      : 0.00
% 3.63/1.62  Index Deletion       : 0.00
% 3.63/1.62  Index Matching       : 0.00
% 3.63/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
