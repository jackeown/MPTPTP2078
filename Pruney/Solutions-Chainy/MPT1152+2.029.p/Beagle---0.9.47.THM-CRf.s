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

% Result     : Theorem 3.39s
% Output     : CNFRefutation 3.62s
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
%$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k4_tarski > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

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
    ! [A_26] :
      ( l1_struct_0(A_26)
      | ~ l1_orders_2(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_51,plain,(
    ! [A_42] :
      ( u1_struct_0(A_42) = k2_struct_0(A_42)
      | ~ l1_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_57,plain,(
    ! [A_44] :
      ( u1_struct_0(A_44) = k2_struct_0(A_44)
      | ~ l1_orders_2(A_44) ) ),
    inference(resolution,[status(thm)],[c_24,c_51])).

tff(c_61,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_57])).

tff(c_14,plain,(
    ! [A_15] :
      ( ~ v1_xboole_0(u1_struct_0(A_15))
      | ~ l1_struct_0(A_15)
      | v2_struct_0(A_15) ) ),
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
    ! [A_45] :
      ( m1_subset_1(k2_struct_0(A_45),k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_struct_0(A_45) ) ),
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
    ! [A_74,B_75] :
      ( k2_orders_2(A_74,B_75) = a_2_1_orders_2(A_74,B_75)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_orders_2(A_74)
      | ~ v5_orders_2(A_74)
      | ~ v4_orders_2(A_74)
      | ~ v3_orders_2(A_74)
      | v2_struct_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_124,plain,(
    ! [B_75] :
      ( k2_orders_2('#skF_4',B_75) = a_2_1_orders_2('#skF_4',B_75)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_118])).

tff(c_127,plain,(
    ! [B_75] :
      ( k2_orders_2('#skF_4',B_75) = a_2_1_orders_2('#skF_4',B_75)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_124])).

tff(c_129,plain,(
    ! [B_76] :
      ( k2_orders_2('#skF_4',B_76) = a_2_1_orders_2('#skF_4',B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
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
    ! [A_78,B_79,C_80] :
      ( '#skF_2'(A_78,B_79,C_80) = A_78
      | ~ r2_hidden(A_78,a_2_1_orders_2(B_79,C_80))
      | ~ m1_subset_1(C_80,k1_zfmisc_1(u1_struct_0(B_79)))
      | ~ l1_orders_2(B_79)
      | ~ v5_orders_2(B_79)
      | ~ v4_orders_2(B_79)
      | ~ v3_orders_2(B_79)
      | v2_struct_0(B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_200,plain,(
    ! [B_93,C_94] :
      ( '#skF_2'('#skF_1'(a_2_1_orders_2(B_93,C_94)),B_93,C_94) = '#skF_1'(a_2_1_orders_2(B_93,C_94))
      | ~ m1_subset_1(C_94,k1_zfmisc_1(u1_struct_0(B_93)))
      | ~ l1_orders_2(B_93)
      | ~ v5_orders_2(B_93)
      | ~ v4_orders_2(B_93)
      | ~ v3_orders_2(B_93)
      | v2_struct_0(B_93)
      | a_2_1_orders_2(B_93,C_94) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_162])).

tff(c_204,plain,(
    ! [C_94] :
      ( '#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4',C_94)),'#skF_4',C_94) = '#skF_1'(a_2_1_orders_2('#skF_4',C_94))
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | a_2_1_orders_2('#skF_4',C_94) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_200])).

tff(c_207,plain,(
    ! [C_94] :
      ( '#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4',C_94)),'#skF_4',C_94) = '#skF_1'(a_2_1_orders_2('#skF_4',C_94))
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | a_2_1_orders_2('#skF_4',C_94) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_204])).

tff(c_209,plain,(
    ! [C_95] :
      ( '#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4',C_95)),'#skF_4',C_95) = '#skF_1'(a_2_1_orders_2('#skF_4',C_95))
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | a_2_1_orders_2('#skF_4',C_95) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_207])).

tff(c_211,plain,
    ( '#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),'#skF_4',k2_struct_0('#skF_4')) = '#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
    | a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_90,c_209])).

tff(c_214,plain,(
    '#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),'#skF_4',k2_struct_0('#skF_4')) = '#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_211])).

tff(c_171,plain,(
    ! [A_81,B_82,C_83] :
      ( m1_subset_1('#skF_2'(A_81,B_82,C_83),u1_struct_0(B_82))
      | ~ r2_hidden(A_81,a_2_1_orders_2(B_82,C_83))
      | ~ m1_subset_1(C_83,k1_zfmisc_1(u1_struct_0(B_82)))
      | ~ l1_orders_2(B_82)
      | ~ v5_orders_2(B_82)
      | ~ v4_orders_2(B_82)
      | ~ v3_orders_2(B_82)
      | v2_struct_0(B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_176,plain,(
    ! [A_81,C_83] :
      ( m1_subset_1('#skF_2'(A_81,'#skF_4',C_83),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_81,a_2_1_orders_2('#skF_4',C_83))
      | ~ m1_subset_1(C_83,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_171])).

tff(c_179,plain,(
    ! [A_81,C_83] :
      ( m1_subset_1('#skF_2'(A_81,'#skF_4',C_83),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_81,a_2_1_orders_2('#skF_4',C_83))
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_61,c_176])).

tff(c_180,plain,(
    ! [A_81,C_83] :
      ( m1_subset_1('#skF_2'(A_81,'#skF_4',C_83),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_81,a_2_1_orders_2('#skF_4',C_83))
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
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
    ! [A_14] :
      ( m1_subset_1(k2_struct_0(A_14),k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_205,plain,(
    ! [A_14] :
      ( '#skF_2'('#skF_1'(a_2_1_orders_2(A_14,k2_struct_0(A_14))),A_14,k2_struct_0(A_14)) = '#skF_1'(a_2_1_orders_2(A_14,k2_struct_0(A_14)))
      | ~ l1_orders_2(A_14)
      | ~ v5_orders_2(A_14)
      | ~ v4_orders_2(A_14)
      | ~ v3_orders_2(A_14)
      | v2_struct_0(A_14)
      | a_2_1_orders_2(A_14,k2_struct_0(A_14)) = k1_xboole_0
      | ~ l1_struct_0(A_14) ) ),
    inference(resolution,[status(thm)],[c_12,c_200])).

tff(c_740,plain,(
    ! [B_156,A_157,C_158,E_159] :
      ( r2_orders_2(B_156,'#skF_2'(A_157,B_156,C_158),E_159)
      | ~ r2_hidden(E_159,C_158)
      | ~ m1_subset_1(E_159,u1_struct_0(B_156))
      | ~ r2_hidden(A_157,a_2_1_orders_2(B_156,C_158))
      | ~ m1_subset_1(C_158,k1_zfmisc_1(u1_struct_0(B_156)))
      | ~ l1_orders_2(B_156)
      | ~ v5_orders_2(B_156)
      | ~ v4_orders_2(B_156)
      | ~ v3_orders_2(B_156)
      | v2_struct_0(B_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_744,plain,(
    ! [A_157,C_158,E_159] :
      ( r2_orders_2('#skF_4','#skF_2'(A_157,'#skF_4',C_158),E_159)
      | ~ r2_hidden(E_159,C_158)
      | ~ m1_subset_1(E_159,u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_157,a_2_1_orders_2('#skF_4',C_158))
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_740])).

tff(c_747,plain,(
    ! [A_157,C_158,E_159] :
      ( r2_orders_2('#skF_4','#skF_2'(A_157,'#skF_4',C_158),E_159)
      | ~ r2_hidden(E_159,C_158)
      | ~ m1_subset_1(E_159,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_157,a_2_1_orders_2('#skF_4',C_158))
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_61,c_744])).

tff(c_749,plain,(
    ! [A_160,C_161,E_162] :
      ( r2_orders_2('#skF_4','#skF_2'(A_160,'#skF_4',C_161),E_162)
      | ~ r2_hidden(E_162,C_161)
      | ~ m1_subset_1(E_162,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_160,a_2_1_orders_2('#skF_4',C_161))
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_747])).

tff(c_753,plain,(
    ! [A_163,E_164] :
      ( r2_orders_2('#skF_4','#skF_2'(A_163,'#skF_4',k2_struct_0('#skF_4')),E_164)
      | ~ r2_hidden(E_164,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_164,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_163,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_90,c_749])).

tff(c_765,plain,(
    ! [E_164] :
      ( r2_orders_2('#skF_4','#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),E_164)
      | ~ r2_hidden(E_164,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_164,k2_struct_0('#skF_4'))
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
    ! [E_164] :
      ( r2_orders_2('#skF_4','#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),E_164)
      | ~ r2_hidden(E_164,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_164,k2_struct_0('#skF_4'))
      | v2_struct_0('#skF_4')
      | a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_46,c_44,c_42,c_40,c_253,c_765])).

tff(c_784,plain,(
    ! [E_165] :
      ( r2_orders_2('#skF_4','#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),E_165)
      | ~ r2_hidden(E_165,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_165,k2_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_48,c_780])).

tff(c_18,plain,(
    ! [A_16,C_22] :
      ( ~ r2_orders_2(A_16,C_22,C_22)
      | ~ m1_subset_1(C_22,u1_struct_0(A_16))
      | ~ l1_orders_2(A_16) ) ),
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
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:16:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.39/1.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.61  
% 3.39/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.61  %$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k4_tarski > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3
% 3.39/1.61  
% 3.39/1.61  %Foreground sorts:
% 3.39/1.61  
% 3.39/1.61  
% 3.39/1.61  %Background operators:
% 3.39/1.61  
% 3.39/1.61  
% 3.39/1.61  %Foreground operators:
% 3.39/1.61  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.39/1.61  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.39/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.39/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.39/1.61  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.39/1.61  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.39/1.61  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.39/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.39/1.61  tff(a_2_1_orders_2, type, a_2_1_orders_2: ($i * $i) > $i).
% 3.39/1.61  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 3.39/1.61  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.39/1.61  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.39/1.61  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.39/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.39/1.62  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.39/1.62  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.39/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.39/1.62  tff('#skF_4', type, '#skF_4': $i).
% 3.39/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.39/1.62  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 3.39/1.62  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.39/1.62  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.39/1.62  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.39/1.62  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.39/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.39/1.62  
% 3.62/1.66  tff(f_139, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k2_orders_2(A, k2_struct_0(A)) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_orders_2)).
% 3.62/1.66  tff(f_98, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 3.62/1.66  tff(f_51, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.62/1.66  tff(f_63, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.62/1.66  tff(f_55, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 3.62/1.66  tff(f_94, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_orders_2(A, B) = a_2_1_orders_2(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_orders_2)).
% 3.62/1.66  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 3.62/1.66  tff(f_125, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_1_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, D, E))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_1_orders_2)).
% 3.62/1.66  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.62/1.66  tff(f_78, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_orders_2)).
% 3.62/1.66  tff(c_40, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.62/1.66  tff(c_24, plain, (![A_26]: (l1_struct_0(A_26) | ~l1_orders_2(A_26))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.62/1.66  tff(c_48, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.62/1.66  tff(c_51, plain, (![A_42]: (u1_struct_0(A_42)=k2_struct_0(A_42) | ~l1_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.62/1.66  tff(c_57, plain, (![A_44]: (u1_struct_0(A_44)=k2_struct_0(A_44) | ~l1_orders_2(A_44))), inference(resolution, [status(thm)], [c_24, c_51])).
% 3.62/1.66  tff(c_61, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_40, c_57])).
% 3.62/1.66  tff(c_14, plain, (![A_15]: (~v1_xboole_0(u1_struct_0(A_15)) | ~l1_struct_0(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.62/1.66  tff(c_65, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_61, c_14])).
% 3.62/1.66  tff(c_68, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_48, c_65])).
% 3.62/1.66  tff(c_70, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_68])).
% 3.62/1.66  tff(c_73, plain, (~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_24, c_70])).
% 3.62/1.66  tff(c_77, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_73])).
% 3.62/1.66  tff(c_78, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_68])).
% 3.62/1.66  tff(c_79, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_68])).
% 3.62/1.66  tff(c_85, plain, (![A_45]: (m1_subset_1(k2_struct_0(A_45), k1_zfmisc_1(u1_struct_0(A_45))) | ~l1_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.62/1.66  tff(c_88, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_61, c_85])).
% 3.62/1.66  tff(c_90, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_88])).
% 3.62/1.66  tff(c_46, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.62/1.66  tff(c_44, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.62/1.66  tff(c_42, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.62/1.66  tff(c_118, plain, (![A_74, B_75]: (k2_orders_2(A_74, B_75)=a_2_1_orders_2(A_74, B_75) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_orders_2(A_74) | ~v5_orders_2(A_74) | ~v4_orders_2(A_74) | ~v3_orders_2(A_74) | v2_struct_0(A_74))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.62/1.66  tff(c_124, plain, (![B_75]: (k2_orders_2('#skF_4', B_75)=a_2_1_orders_2('#skF_4', B_75) | ~m1_subset_1(B_75, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_61, c_118])).
% 3.62/1.66  tff(c_127, plain, (![B_75]: (k2_orders_2('#skF_4', B_75)=a_2_1_orders_2('#skF_4', B_75) | ~m1_subset_1(B_75, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_124])).
% 3.62/1.66  tff(c_129, plain, (![B_76]: (k2_orders_2('#skF_4', B_76)=a_2_1_orders_2('#skF_4', B_76) | ~m1_subset_1(B_76, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_48, c_127])).
% 3.62/1.66  tff(c_133, plain, (k2_orders_2('#skF_4', k2_struct_0('#skF_4'))=a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_90, c_129])).
% 3.62/1.66  tff(c_38, plain, (k2_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.62/1.66  tff(c_134, plain, (a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_133, c_38])).
% 3.62/1.66  tff(c_4, plain, (![A_3]: (r2_hidden('#skF_1'(A_3), A_3) | k1_xboole_0=A_3)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.62/1.66  tff(c_162, plain, (![A_78, B_79, C_80]: ('#skF_2'(A_78, B_79, C_80)=A_78 | ~r2_hidden(A_78, a_2_1_orders_2(B_79, C_80)) | ~m1_subset_1(C_80, k1_zfmisc_1(u1_struct_0(B_79))) | ~l1_orders_2(B_79) | ~v5_orders_2(B_79) | ~v4_orders_2(B_79) | ~v3_orders_2(B_79) | v2_struct_0(B_79))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.62/1.66  tff(c_200, plain, (![B_93, C_94]: ('#skF_2'('#skF_1'(a_2_1_orders_2(B_93, C_94)), B_93, C_94)='#skF_1'(a_2_1_orders_2(B_93, C_94)) | ~m1_subset_1(C_94, k1_zfmisc_1(u1_struct_0(B_93))) | ~l1_orders_2(B_93) | ~v5_orders_2(B_93) | ~v4_orders_2(B_93) | ~v3_orders_2(B_93) | v2_struct_0(B_93) | a_2_1_orders_2(B_93, C_94)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_162])).
% 3.62/1.66  tff(c_204, plain, (![C_94]: ('#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4', C_94)), '#skF_4', C_94)='#skF_1'(a_2_1_orders_2('#skF_4', C_94)) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | a_2_1_orders_2('#skF_4', C_94)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_61, c_200])).
% 3.62/1.66  tff(c_207, plain, (![C_94]: ('#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4', C_94)), '#skF_4', C_94)='#skF_1'(a_2_1_orders_2('#skF_4', C_94)) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | a_2_1_orders_2('#skF_4', C_94)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_204])).
% 3.62/1.66  tff(c_209, plain, (![C_95]: ('#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4', C_95)), '#skF_4', C_95)='#skF_1'(a_2_1_orders_2('#skF_4', C_95)) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_struct_0('#skF_4'))) | a_2_1_orders_2('#skF_4', C_95)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_48, c_207])).
% 3.62/1.66  tff(c_211, plain, ('#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), '#skF_4', k2_struct_0('#skF_4'))='#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_90, c_209])).
% 3.62/1.66  tff(c_214, plain, ('#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), '#skF_4', k2_struct_0('#skF_4'))='#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_134, c_211])).
% 3.62/1.66  tff(c_171, plain, (![A_81, B_82, C_83]: (m1_subset_1('#skF_2'(A_81, B_82, C_83), u1_struct_0(B_82)) | ~r2_hidden(A_81, a_2_1_orders_2(B_82, C_83)) | ~m1_subset_1(C_83, k1_zfmisc_1(u1_struct_0(B_82))) | ~l1_orders_2(B_82) | ~v5_orders_2(B_82) | ~v4_orders_2(B_82) | ~v3_orders_2(B_82) | v2_struct_0(B_82))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.62/1.66  tff(c_176, plain, (![A_81, C_83]: (m1_subset_1('#skF_2'(A_81, '#skF_4', C_83), k2_struct_0('#skF_4')) | ~r2_hidden(A_81, a_2_1_orders_2('#skF_4', C_83)) | ~m1_subset_1(C_83, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_61, c_171])).
% 3.62/1.66  tff(c_179, plain, (![A_81, C_83]: (m1_subset_1('#skF_2'(A_81, '#skF_4', C_83), k2_struct_0('#skF_4')) | ~r2_hidden(A_81, a_2_1_orders_2('#skF_4', C_83)) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_61, c_176])).
% 3.62/1.66  tff(c_180, plain, (![A_81, C_83]: (m1_subset_1('#skF_2'(A_81, '#skF_4', C_83), k2_struct_0('#skF_4')) | ~r2_hidden(A_81, a_2_1_orders_2('#skF_4', C_83)) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_48, c_179])).
% 3.62/1.66  tff(c_218, plain, (m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_214, c_180])).
% 3.62/1.66  tff(c_225, plain, (m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_218])).
% 3.62/1.66  tff(c_239, plain, (~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_225])).
% 3.62/1.66  tff(c_245, plain, (a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_239])).
% 3.62/1.66  tff(c_251, plain, $false, inference(negUnitSimplification, [status(thm)], [c_134, c_245])).
% 3.62/1.66  tff(c_252, plain, (m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_225])).
% 3.62/1.66  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.62/1.66  tff(c_253, plain, (r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_225])).
% 3.62/1.66  tff(c_12, plain, (![A_14]: (m1_subset_1(k2_struct_0(A_14), k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.62/1.66  tff(c_205, plain, (![A_14]: ('#skF_2'('#skF_1'(a_2_1_orders_2(A_14, k2_struct_0(A_14))), A_14, k2_struct_0(A_14))='#skF_1'(a_2_1_orders_2(A_14, k2_struct_0(A_14))) | ~l1_orders_2(A_14) | ~v5_orders_2(A_14) | ~v4_orders_2(A_14) | ~v3_orders_2(A_14) | v2_struct_0(A_14) | a_2_1_orders_2(A_14, k2_struct_0(A_14))=k1_xboole_0 | ~l1_struct_0(A_14))), inference(resolution, [status(thm)], [c_12, c_200])).
% 3.62/1.66  tff(c_740, plain, (![B_156, A_157, C_158, E_159]: (r2_orders_2(B_156, '#skF_2'(A_157, B_156, C_158), E_159) | ~r2_hidden(E_159, C_158) | ~m1_subset_1(E_159, u1_struct_0(B_156)) | ~r2_hidden(A_157, a_2_1_orders_2(B_156, C_158)) | ~m1_subset_1(C_158, k1_zfmisc_1(u1_struct_0(B_156))) | ~l1_orders_2(B_156) | ~v5_orders_2(B_156) | ~v4_orders_2(B_156) | ~v3_orders_2(B_156) | v2_struct_0(B_156))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.62/1.66  tff(c_744, plain, (![A_157, C_158, E_159]: (r2_orders_2('#skF_4', '#skF_2'(A_157, '#skF_4', C_158), E_159) | ~r2_hidden(E_159, C_158) | ~m1_subset_1(E_159, u1_struct_0('#skF_4')) | ~r2_hidden(A_157, a_2_1_orders_2('#skF_4', C_158)) | ~m1_subset_1(C_158, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_61, c_740])).
% 3.62/1.66  tff(c_747, plain, (![A_157, C_158, E_159]: (r2_orders_2('#skF_4', '#skF_2'(A_157, '#skF_4', C_158), E_159) | ~r2_hidden(E_159, C_158) | ~m1_subset_1(E_159, k2_struct_0('#skF_4')) | ~r2_hidden(A_157, a_2_1_orders_2('#skF_4', C_158)) | ~m1_subset_1(C_158, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_61, c_744])).
% 3.62/1.66  tff(c_749, plain, (![A_160, C_161, E_162]: (r2_orders_2('#skF_4', '#skF_2'(A_160, '#skF_4', C_161), E_162) | ~r2_hidden(E_162, C_161) | ~m1_subset_1(E_162, k2_struct_0('#skF_4')) | ~r2_hidden(A_160, a_2_1_orders_2('#skF_4', C_161)) | ~m1_subset_1(C_161, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_48, c_747])).
% 3.62/1.66  tff(c_753, plain, (![A_163, E_164]: (r2_orders_2('#skF_4', '#skF_2'(A_163, '#skF_4', k2_struct_0('#skF_4')), E_164) | ~r2_hidden(E_164, k2_struct_0('#skF_4')) | ~m1_subset_1(E_164, k2_struct_0('#skF_4')) | ~r2_hidden(A_163, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_90, c_749])).
% 3.62/1.66  tff(c_765, plain, (![E_164]: (r2_orders_2('#skF_4', '#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), E_164) | ~r2_hidden(E_164, k2_struct_0('#skF_4')) | ~m1_subset_1(E_164, k2_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0 | ~l1_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_205, c_753])).
% 3.62/1.66  tff(c_780, plain, (![E_164]: (r2_orders_2('#skF_4', '#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), E_164) | ~r2_hidden(E_164, k2_struct_0('#skF_4')) | ~m1_subset_1(E_164, k2_struct_0('#skF_4')) | v2_struct_0('#skF_4') | a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_79, c_46, c_44, c_42, c_40, c_253, c_765])).
% 3.62/1.66  tff(c_784, plain, (![E_165]: (r2_orders_2('#skF_4', '#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), E_165) | ~r2_hidden(E_165, k2_struct_0('#skF_4')) | ~m1_subset_1(E_165, k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_134, c_48, c_780])).
% 3.62/1.66  tff(c_18, plain, (![A_16, C_22]: (~r2_orders_2(A_16, C_22, C_22) | ~m1_subset_1(C_22, u1_struct_0(A_16)) | ~l1_orders_2(A_16))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.62/1.66  tff(c_792, plain, (~m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_784, c_18])).
% 3.62/1.66  tff(c_802, plain, (~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_252, c_40, c_252, c_61, c_792])).
% 3.62/1.66  tff(c_805, plain, (v1_xboole_0(k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_2, c_802])).
% 3.62/1.66  tff(c_808, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_252, c_805])).
% 3.62/1.66  tff(c_810, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_808])).
% 3.62/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.62/1.66  
% 3.62/1.66  Inference rules
% 3.62/1.66  ----------------------
% 3.62/1.66  #Ref     : 0
% 3.62/1.66  #Sup     : 145
% 3.62/1.66  #Fact    : 0
% 3.62/1.66  #Define  : 0
% 3.62/1.66  #Split   : 4
% 3.62/1.66  #Chain   : 0
% 3.62/1.66  #Close   : 0
% 3.62/1.66  
% 3.62/1.66  Ordering : KBO
% 3.62/1.66  
% 3.62/1.66  Simplification rules
% 3.62/1.66  ----------------------
% 3.62/1.66  #Subsume      : 13
% 3.62/1.66  #Demod        : 335
% 3.62/1.66  #Tautology    : 50
% 3.62/1.66  #SimpNegUnit  : 51
% 3.62/1.66  #BackRed      : 19
% 3.62/1.66  
% 3.62/1.66  #Partial instantiations: 0
% 3.62/1.66  #Strategies tried      : 1
% 3.62/1.66  
% 3.62/1.66  Timing (in seconds)
% 3.62/1.66  ----------------------
% 3.74/1.66  Preprocessing        : 0.33
% 3.74/1.66  Parsing              : 0.17
% 3.74/1.66  CNF conversion       : 0.03
% 3.74/1.66  Main loop            : 0.49
% 3.74/1.66  Inferencing          : 0.18
% 3.74/1.66  Reduction            : 0.16
% 3.74/1.66  Demodulation         : 0.10
% 3.74/1.66  BG Simplification    : 0.03
% 3.74/1.66  Subsumption          : 0.09
% 3.74/1.67  Abstraction          : 0.03
% 3.74/1.67  MUC search           : 0.00
% 3.74/1.67  Cooper               : 0.00
% 3.74/1.67  Total                : 0.88
% 3.74/1.67  Index Insertion      : 0.00
% 3.74/1.67  Index Deletion       : 0.00
% 3.74/1.67  Index Matching       : 0.00
% 3.74/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
