%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:26 EST 2020

% Result     : Theorem 29.69s
% Output     : CNFRefutation 29.69s
% Verified   : 
% Statistics : Number of formulae       :  155 (2026 expanded)
%              Number of leaves         :   48 ( 770 expanded)
%              Depth                    :   20
%              Number of atoms          :  438 (6115 expanded)
%              Number of equality atoms :   58 (1221 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r2_orders_2 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k4_tarski > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff(k1_orders_2,type,(
    k1_orders_2: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(a_2_0_orders_2,type,(
    a_2_0_orders_2: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_struct_0,type,(
    k1_struct_0: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_36,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_38,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_200,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => k1_orders_2(A,k2_struct_0(A)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_orders_2)).

tff(f_103,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_99,axiom,(
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

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_71,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_130,axiom,(
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

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k1_struct_0(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_struct_0)).

tff(f_186,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => k1_orders_2(A,k1_struct_0(A)) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_orders_2)).

tff(f_40,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_158,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => r3_orders_2(A,B,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

tff(f_145,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_173,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ~ ( r1_orders_2(A,B,C)
                  & r2_orders_2(A,C,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_orders_2)).

tff(c_10,plain,(
    ! [A_7] : k2_subset_1(A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_12,plain,(
    ! [A_8] : m1_subset_1(k2_subset_1(A_8),k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_73,plain,(
    ! [A_8] : m1_subset_1(A_8,k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_70,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_68,plain,(
    v4_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_66,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_64,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_38,plain,(
    ! [A_33] :
      ( l1_struct_0(A_33)
      | ~ l1_orders_2(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_102,plain,(
    ! [A_70] :
      ( u1_struct_0(A_70) = k2_struct_0(A_70)
      | ~ l1_struct_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_112,plain,(
    ! [A_72] :
      ( u1_struct_0(A_72) = k2_struct_0(A_72)
      | ~ l1_orders_2(A_72) ) ),
    inference(resolution,[status(thm)],[c_38,c_102])).

tff(c_116,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_112])).

tff(c_15302,plain,(
    ! [A_727,B_728] :
      ( k1_orders_2(A_727,B_728) = a_2_0_orders_2(A_727,B_728)
      | ~ m1_subset_1(B_728,k1_zfmisc_1(u1_struct_0(A_727)))
      | ~ l1_orders_2(A_727)
      | ~ v5_orders_2(A_727)
      | ~ v4_orders_2(A_727)
      | ~ v3_orders_2(A_727)
      | v2_struct_0(A_727) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_15320,plain,(
    ! [B_728] :
      ( k1_orders_2('#skF_5',B_728) = a_2_0_orders_2('#skF_5',B_728)
      | ~ m1_subset_1(B_728,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_15302])).

tff(c_15334,plain,(
    ! [B_728] :
      ( k1_orders_2('#skF_5',B_728) = a_2_0_orders_2('#skF_5',B_728)
      | ~ m1_subset_1(B_728,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_15320])).

tff(c_15372,plain,(
    ! [B_732] :
      ( k1_orders_2('#skF_5',B_732) = a_2_0_orders_2('#skF_5',B_732)
      | ~ m1_subset_1(B_732,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_15334])).

tff(c_15401,plain,(
    k1_orders_2('#skF_5',k2_struct_0('#skF_5')) = a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_73,c_15372])).

tff(c_62,plain,(
    k1_orders_2('#skF_5',k2_struct_0('#skF_5')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_15408,plain,(
    a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_15401,c_62])).

tff(c_129,plain,(
    ! [A_76,B_77] :
      ( r1_tarski(A_76,B_77)
      | ~ m1_subset_1(A_76,k1_zfmisc_1(B_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_140,plain,(
    ! [A_8] : r1_tarski(A_8,A_8) ),
    inference(resolution,[status(thm)],[c_73,c_129])).

tff(c_24,plain,(
    ! [A_17] :
      ( r2_hidden('#skF_2'(A_17),A_17)
      | k1_xboole_0 = A_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_177,plain,(
    ! [C_87,B_88,A_89] :
      ( r2_hidden(C_87,B_88)
      | ~ r2_hidden(C_87,A_89)
      | ~ r1_tarski(A_89,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_183,plain,(
    ! [A_17,B_88] :
      ( r2_hidden('#skF_2'(A_17),B_88)
      | ~ r1_tarski(A_17,B_88)
      | k1_xboole_0 = A_17 ) ),
    inference(resolution,[status(thm)],[c_24,c_177])).

tff(c_15849,plain,(
    ! [A_756,B_757,C_758] :
      ( '#skF_3'(A_756,B_757,C_758) = A_756
      | ~ r2_hidden(A_756,a_2_0_orders_2(B_757,C_758))
      | ~ m1_subset_1(C_758,k1_zfmisc_1(u1_struct_0(B_757)))
      | ~ l1_orders_2(B_757)
      | ~ v5_orders_2(B_757)
      | ~ v4_orders_2(B_757)
      | ~ v3_orders_2(B_757)
      | v2_struct_0(B_757) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_42374,plain,(
    ! [B_1592,C_1593] :
      ( '#skF_3'('#skF_2'(a_2_0_orders_2(B_1592,C_1593)),B_1592,C_1593) = '#skF_2'(a_2_0_orders_2(B_1592,C_1593))
      | ~ m1_subset_1(C_1593,k1_zfmisc_1(u1_struct_0(B_1592)))
      | ~ l1_orders_2(B_1592)
      | ~ v5_orders_2(B_1592)
      | ~ v4_orders_2(B_1592)
      | ~ v3_orders_2(B_1592)
      | v2_struct_0(B_1592)
      | a_2_0_orders_2(B_1592,C_1593) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_24,c_15849])).

tff(c_42405,plain,(
    ! [C_1593] :
      ( '#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5',C_1593)),'#skF_5',C_1593) = '#skF_2'(a_2_0_orders_2('#skF_5',C_1593))
      | ~ m1_subset_1(C_1593,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | a_2_0_orders_2('#skF_5',C_1593) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_42374])).

tff(c_42423,plain,(
    ! [C_1593] :
      ( '#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5',C_1593)),'#skF_5',C_1593) = '#skF_2'(a_2_0_orders_2('#skF_5',C_1593))
      | ~ m1_subset_1(C_1593,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | v2_struct_0('#skF_5')
      | a_2_0_orders_2('#skF_5',C_1593) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_42405])).

tff(c_42738,plain,(
    ! [C_1609] :
      ( '#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5',C_1609)),'#skF_5',C_1609) = '#skF_2'(a_2_0_orders_2('#skF_5',C_1609))
      | ~ m1_subset_1(C_1609,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | a_2_0_orders_2('#skF_5',C_1609) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_42423])).

tff(c_42768,plain,
    ( '#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),'#skF_5',k2_struct_0('#skF_5')) = '#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')))
    | a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_73,c_42738])).

tff(c_42785,plain,(
    '#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),'#skF_5',k2_struct_0('#skF_5')) = '#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_15408,c_42768])).

tff(c_50,plain,(
    ! [A_34,B_35,C_36] :
      ( m1_subset_1('#skF_3'(A_34,B_35,C_36),u1_struct_0(B_35))
      | ~ r2_hidden(A_34,a_2_0_orders_2(B_35,C_36))
      | ~ m1_subset_1(C_36,k1_zfmisc_1(u1_struct_0(B_35)))
      | ~ l1_orders_2(B_35)
      | ~ v5_orders_2(B_35)
      | ~ v4_orders_2(B_35)
      | ~ v3_orders_2(B_35)
      | v2_struct_0(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_44041,plain,
    ( m1_subset_1('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),u1_struct_0('#skF_5'))
    | ~ r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')))
    | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_42785,c_50])).

tff(c_44055,plain,
    ( m1_subset_1('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),k2_struct_0('#skF_5'))
    | ~ r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_73,c_116,c_116,c_44041])).

tff(c_44056,plain,
    ( m1_subset_1('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),k2_struct_0('#skF_5'))
    | ~ r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_44055])).

tff(c_44161,plain,(
    ~ r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_44056])).

tff(c_44164,plain,
    ( ~ r1_tarski(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')),a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')))
    | a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_183,c_44161])).

tff(c_44170,plain,(
    a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_44164])).

tff(c_44172,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15408,c_44170])).

tff(c_44173,plain,(
    m1_subset_1('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),k2_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_44056])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_87,plain,(
    ! [A_66] :
      ( k1_struct_0(A_66) = k1_xboole_0
      | ~ l1_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_92,plain,(
    ! [A_67] :
      ( k1_struct_0(A_67) = k1_xboole_0
      | ~ l1_orders_2(A_67) ) ),
    inference(resolution,[status(thm)],[c_38,c_87])).

tff(c_96,plain,(
    k1_struct_0('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_64,c_92])).

tff(c_288,plain,(
    ! [A_111] :
      ( k1_orders_2(A_111,k1_struct_0(A_111)) = u1_struct_0(A_111)
      | ~ l1_orders_2(A_111)
      | ~ v5_orders_2(A_111)
      | ~ v4_orders_2(A_111)
      | ~ v3_orders_2(A_111)
      | v2_struct_0(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_297,plain,
    ( k1_orders_2('#skF_5',k1_xboole_0) = u1_struct_0('#skF_5')
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_288])).

tff(c_301,plain,
    ( k1_orders_2('#skF_5',k1_xboole_0) = k2_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_116,c_297])).

tff(c_302,plain,(
    k1_orders_2('#skF_5',k1_xboole_0) = k2_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_301])).

tff(c_14,plain,(
    ! [A_9] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_15396,plain,(
    k1_orders_2('#skF_5',k1_xboole_0) = a_2_0_orders_2('#skF_5',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_15372])).

tff(c_15403,plain,(
    a_2_0_orders_2('#skF_5',k1_xboole_0) = k2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_302,c_15396])).

tff(c_16333,plain,(
    ! [D_782,B_783,C_784] :
      ( r2_hidden('#skF_4'(D_782,B_783,C_784,D_782),C_784)
      | r2_hidden(D_782,a_2_0_orders_2(B_783,C_784))
      | ~ m1_subset_1(D_782,u1_struct_0(B_783))
      | ~ m1_subset_1(C_784,k1_zfmisc_1(u1_struct_0(B_783)))
      | ~ l1_orders_2(B_783)
      | ~ v5_orders_2(B_783)
      | ~ v4_orders_2(B_783)
      | ~ v3_orders_2(B_783)
      | v2_struct_0(B_783) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_16352,plain,(
    ! [D_782,C_784] :
      ( r2_hidden('#skF_4'(D_782,'#skF_5',C_784,D_782),C_784)
      | r2_hidden(D_782,a_2_0_orders_2('#skF_5',C_784))
      | ~ m1_subset_1(D_782,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_784,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_16333])).

tff(c_16366,plain,(
    ! [D_782,C_784] :
      ( r2_hidden('#skF_4'(D_782,'#skF_5',C_784,D_782),C_784)
      | r2_hidden(D_782,a_2_0_orders_2('#skF_5',C_784))
      | ~ m1_subset_1(D_782,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_784,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_116,c_16352])).

tff(c_16450,plain,(
    ! [D_794,C_795] :
      ( r2_hidden('#skF_4'(D_794,'#skF_5',C_795,D_794),C_795)
      | r2_hidden(D_794,a_2_0_orders_2('#skF_5',C_795))
      | ~ m1_subset_1(D_794,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_795,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_16366])).

tff(c_16471,plain,(
    ! [D_794] :
      ( r2_hidden('#skF_4'(D_794,'#skF_5',k1_xboole_0,D_794),k1_xboole_0)
      | r2_hidden(D_794,a_2_0_orders_2('#skF_5',k1_xboole_0))
      | ~ m1_subset_1(D_794,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_14,c_16450])).

tff(c_41649,plain,(
    ! [D_1570] :
      ( r2_hidden('#skF_4'(D_1570,'#skF_5',k1_xboole_0,D_1570),k1_xboole_0)
      | r2_hidden(D_1570,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(D_1570,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15403,c_16471])).

tff(c_22,plain,(
    ! [B_16,A_15] :
      ( ~ r1_tarski(B_16,A_15)
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_41665,plain,(
    ! [D_1570] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_4'(D_1570,'#skF_5',k1_xboole_0,D_1570))
      | r2_hidden(D_1570,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(D_1570,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_41649,c_22])).

tff(c_41680,plain,(
    ! [D_1570] :
      ( r2_hidden(D_1570,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(D_1570,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_41665])).

tff(c_41768,plain,(
    ! [D_1573] :
      ( r2_hidden(D_1573,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(D_1573,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_41665])).

tff(c_15854,plain,(
    ! [A_756] :
      ( '#skF_3'(A_756,'#skF_5',k1_xboole_0) = A_756
      | ~ r2_hidden(A_756,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15403,c_15849])).

tff(c_15866,plain,(
    ! [A_756] :
      ( '#skF_3'(A_756,'#skF_5',k1_xboole_0) = A_756
      | ~ r2_hidden(A_756,k2_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_14,c_116,c_15854])).

tff(c_15867,plain,(
    ! [A_756] :
      ( '#skF_3'(A_756,'#skF_5',k1_xboole_0) = A_756
      | ~ r2_hidden(A_756,k2_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_15866])).

tff(c_41797,plain,(
    ! [D_1573] :
      ( '#skF_3'(D_1573,'#skF_5',k1_xboole_0) = D_1573
      | ~ m1_subset_1(D_1573,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_41768,c_15867])).

tff(c_44182,plain,(
    '#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),'#skF_5',k1_xboole_0) = '#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_44173,c_41797])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_17280,plain,(
    ! [B_838,E_839,A_840,C_841] :
      ( r2_orders_2(B_838,E_839,'#skF_3'(A_840,B_838,C_841))
      | ~ r2_hidden(E_839,C_841)
      | ~ m1_subset_1(E_839,u1_struct_0(B_838))
      | ~ r2_hidden(A_840,a_2_0_orders_2(B_838,C_841))
      | ~ m1_subset_1(C_841,k1_zfmisc_1(u1_struct_0(B_838)))
      | ~ l1_orders_2(B_838)
      | ~ v5_orders_2(B_838)
      | ~ v4_orders_2(B_838)
      | ~ v3_orders_2(B_838)
      | v2_struct_0(B_838) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_17311,plain,(
    ! [B_838,E_839,A_840,A_10] :
      ( r2_orders_2(B_838,E_839,'#skF_3'(A_840,B_838,A_10))
      | ~ r2_hidden(E_839,A_10)
      | ~ m1_subset_1(E_839,u1_struct_0(B_838))
      | ~ r2_hidden(A_840,a_2_0_orders_2(B_838,A_10))
      | ~ l1_orders_2(B_838)
      | ~ v5_orders_2(B_838)
      | ~ v4_orders_2(B_838)
      | ~ v3_orders_2(B_838)
      | v2_struct_0(B_838)
      | ~ r1_tarski(A_10,u1_struct_0(B_838)) ) ),
    inference(resolution,[status(thm)],[c_18,c_17280])).

tff(c_44430,plain,(
    ! [E_839] :
      ( r2_orders_2('#skF_5',E_839,'#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))))
      | ~ r2_hidden(E_839,k1_xboole_0)
      | ~ m1_subset_1(E_839,u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),a_2_0_orders_2('#skF_5',k1_xboole_0))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r1_tarski(k1_xboole_0,u1_struct_0('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44182,c_17311])).

tff(c_44443,plain,(
    ! [E_839] :
      ( r2_orders_2('#skF_5',E_839,'#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))))
      | ~ r2_hidden(E_839,k1_xboole_0)
      | ~ m1_subset_1(E_839,k2_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),k2_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_116,c_70,c_68,c_66,c_64,c_15403,c_116,c_44430])).

tff(c_44444,plain,(
    ! [E_839] :
      ( r2_orders_2('#skF_5',E_839,'#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))))
      | ~ r2_hidden(E_839,k1_xboole_0)
      | ~ m1_subset_1(E_839,k2_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),k2_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_44443])).

tff(c_44601,plain,(
    ~ r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),k2_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_44444])).

tff(c_44607,plain,(
    ~ m1_subset_1('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_41680,c_44601])).

tff(c_44615,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44173,c_44607])).

tff(c_44617,plain,(
    r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),k2_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_44444])).

tff(c_237,plain,(
    ! [A_103,C_104,B_105] :
      ( m1_subset_1(A_103,C_104)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(C_104))
      | ~ r2_hidden(A_103,B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_250,plain,(
    ! [A_106,A_107] :
      ( m1_subset_1(A_106,A_107)
      | ~ r2_hidden(A_106,A_107) ) ),
    inference(resolution,[status(thm)],[c_73,c_237])).

tff(c_262,plain,(
    ! [A_17] :
      ( m1_subset_1('#skF_2'(A_17),A_17)
      | k1_xboole_0 = A_17 ) ),
    inference(resolution,[status(thm)],[c_24,c_250])).

tff(c_15084,plain,(
    ! [A_708,B_709,C_710] :
      ( r3_orders_2(A_708,B_709,B_709)
      | ~ m1_subset_1(C_710,u1_struct_0(A_708))
      | ~ m1_subset_1(B_709,u1_struct_0(A_708))
      | ~ l1_orders_2(A_708)
      | ~ v3_orders_2(A_708)
      | v2_struct_0(A_708) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_15092,plain,(
    ! [B_709,C_710] :
      ( r3_orders_2('#skF_5',B_709,B_709)
      | ~ m1_subset_1(C_710,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(B_709,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_15084])).

tff(c_15096,plain,(
    ! [B_709,C_710] :
      ( r3_orders_2('#skF_5',B_709,B_709)
      | ~ m1_subset_1(C_710,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(B_709,k2_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_64,c_116,c_15092])).

tff(c_15097,plain,(
    ! [B_709,C_710] :
      ( r3_orders_2('#skF_5',B_709,B_709)
      | ~ m1_subset_1(C_710,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(B_709,k2_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_15096])).

tff(c_15140,plain,(
    ! [C_712] : ~ m1_subset_1(C_712,k2_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_15097])).

tff(c_15150,plain,(
    k2_struct_0('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_262,c_15140])).

tff(c_15152,plain,(
    k1_orders_2('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_15150,c_302])).

tff(c_15154,plain,(
    k1_orders_2('#skF_5',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_15150,c_62])).

tff(c_15204,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15152,c_15154])).

tff(c_15205,plain,(
    ! [B_709] :
      ( r3_orders_2('#skF_5',B_709,B_709)
      | ~ m1_subset_1(B_709,k2_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_15097])).

tff(c_44184,plain,(
    r3_orders_2('#skF_5','#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),'#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')))) ),
    inference(resolution,[status(thm)],[c_44173,c_15205])).

tff(c_54,plain,(
    ! [A_47,B_48,C_49] :
      ( r1_orders_2(A_47,B_48,C_49)
      | ~ r3_orders_2(A_47,B_48,C_49)
      | ~ m1_subset_1(C_49,u1_struct_0(A_47))
      | ~ m1_subset_1(B_48,u1_struct_0(A_47))
      | ~ l1_orders_2(A_47)
      | ~ v3_orders_2(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_44269,plain,
    ( r1_orders_2('#skF_5','#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),'#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))))
    | ~ m1_subset_1('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_44184,c_54])).

tff(c_44272,plain,
    ( r1_orders_2('#skF_5','#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),'#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_64,c_44173,c_116,c_44269])).

tff(c_44273,plain,(
    r1_orders_2('#skF_5','#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),'#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')))) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_44272])).

tff(c_44174,plain,(
    r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_44056])).

tff(c_42421,plain,(
    ! [B_1592,A_10] :
      ( '#skF_3'('#skF_2'(a_2_0_orders_2(B_1592,A_10)),B_1592,A_10) = '#skF_2'(a_2_0_orders_2(B_1592,A_10))
      | ~ l1_orders_2(B_1592)
      | ~ v5_orders_2(B_1592)
      | ~ v4_orders_2(B_1592)
      | ~ v3_orders_2(B_1592)
      | v2_struct_0(B_1592)
      | a_2_0_orders_2(B_1592,A_10) = k1_xboole_0
      | ~ r1_tarski(A_10,u1_struct_0(B_1592)) ) ),
    inference(resolution,[status(thm)],[c_18,c_42374])).

tff(c_43514,plain,(
    ! [B_1625,E_1626,A_1627] :
      ( r2_orders_2(B_1625,E_1626,'#skF_3'(A_1627,B_1625,u1_struct_0(B_1625)))
      | ~ r2_hidden(E_1626,u1_struct_0(B_1625))
      | ~ m1_subset_1(E_1626,u1_struct_0(B_1625))
      | ~ r2_hidden(A_1627,a_2_0_orders_2(B_1625,u1_struct_0(B_1625)))
      | ~ l1_orders_2(B_1625)
      | ~ v5_orders_2(B_1625)
      | ~ v4_orders_2(B_1625)
      | ~ v3_orders_2(B_1625)
      | v2_struct_0(B_1625) ) ),
    inference(resolution,[status(thm)],[c_73,c_17280])).

tff(c_58,plain,(
    ! [A_53,C_59,B_57] :
      ( ~ r2_orders_2(A_53,C_59,B_57)
      | ~ r1_orders_2(A_53,B_57,C_59)
      | ~ m1_subset_1(C_59,u1_struct_0(A_53))
      | ~ m1_subset_1(B_57,u1_struct_0(A_53))
      | ~ l1_orders_2(A_53)
      | ~ v5_orders_2(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_86463,plain,(
    ! [B_2200,A_2201,E_2202] :
      ( ~ r1_orders_2(B_2200,'#skF_3'(A_2201,B_2200,u1_struct_0(B_2200)),E_2202)
      | ~ m1_subset_1('#skF_3'(A_2201,B_2200,u1_struct_0(B_2200)),u1_struct_0(B_2200))
      | ~ r2_hidden(E_2202,u1_struct_0(B_2200))
      | ~ m1_subset_1(E_2202,u1_struct_0(B_2200))
      | ~ r2_hidden(A_2201,a_2_0_orders_2(B_2200,u1_struct_0(B_2200)))
      | ~ l1_orders_2(B_2200)
      | ~ v5_orders_2(B_2200)
      | ~ v4_orders_2(B_2200)
      | ~ v3_orders_2(B_2200)
      | v2_struct_0(B_2200) ) ),
    inference(resolution,[status(thm)],[c_43514,c_58])).

tff(c_86475,plain,(
    ! [A_2201,E_2202] :
      ( ~ r1_orders_2('#skF_5','#skF_3'(A_2201,'#skF_5',k2_struct_0('#skF_5')),E_2202)
      | ~ m1_subset_1('#skF_3'(A_2201,'#skF_5',u1_struct_0('#skF_5')),u1_struct_0('#skF_5'))
      | ~ r2_hidden(E_2202,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(E_2202,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_2201,a_2_0_orders_2('#skF_5',u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_86463])).

tff(c_86481,plain,(
    ! [A_2201,E_2202] :
      ( ~ r1_orders_2('#skF_5','#skF_3'(A_2201,'#skF_5',k2_struct_0('#skF_5')),E_2202)
      | ~ m1_subset_1('#skF_3'(A_2201,'#skF_5',k2_struct_0('#skF_5')),k2_struct_0('#skF_5'))
      | ~ r2_hidden(E_2202,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(E_2202,k2_struct_0('#skF_5'))
      | ~ r2_hidden(A_2201,a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_116,c_116,c_116,c_116,c_116,c_86475])).

tff(c_86733,plain,(
    ! [A_2206,E_2207] :
      ( ~ r1_orders_2('#skF_5','#skF_3'(A_2206,'#skF_5',k2_struct_0('#skF_5')),E_2207)
      | ~ m1_subset_1('#skF_3'(A_2206,'#skF_5',k2_struct_0('#skF_5')),k2_struct_0('#skF_5'))
      | ~ r2_hidden(E_2207,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(E_2207,k2_struct_0('#skF_5'))
      | ~ r2_hidden(A_2206,a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_86481])).

tff(c_86747,plain,(
    ! [E_2207] :
      ( ~ r1_orders_2('#skF_5','#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),E_2207)
      | ~ m1_subset_1('#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),'#skF_5',k2_struct_0('#skF_5')),k2_struct_0('#skF_5'))
      | ~ r2_hidden(E_2207,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(E_2207,k2_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')) = k1_xboole_0
      | ~ r1_tarski(k2_struct_0('#skF_5'),u1_struct_0('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42421,c_86733])).

tff(c_86760,plain,(
    ! [E_2207] :
      ( ~ r1_orders_2('#skF_5','#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),E_2207)
      | ~ r2_hidden(E_2207,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(E_2207,k2_struct_0('#skF_5'))
      | v2_struct_0('#skF_5')
      | a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_116,c_70,c_68,c_66,c_64,c_44174,c_44173,c_42785,c_86747])).

tff(c_87400,plain,(
    ! [E_2222] :
      ( ~ r1_orders_2('#skF_5','#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),E_2222)
      | ~ r2_hidden(E_2222,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(E_2222,k2_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_15408,c_72,c_86760])).

tff(c_87403,plain,
    ( ~ r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),k2_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_44273,c_87400])).

tff(c_87411,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44173,c_44617,c_87403])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:49:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 29.69/17.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 29.69/17.45  
% 29.69/17.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 29.69/17.46  %$ r3_orders_2 > r2_orders_2 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k4_tarski > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_4 > #skF_3 > #skF_1
% 29.69/17.46  
% 29.69/17.46  %Foreground sorts:
% 29.69/17.46  
% 29.69/17.46  
% 29.69/17.46  %Background operators:
% 29.69/17.46  
% 29.69/17.46  
% 29.69/17.46  %Foreground operators:
% 29.69/17.46  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 29.69/17.46  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 29.69/17.46  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 29.69/17.46  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 29.69/17.46  tff('#skF_2', type, '#skF_2': $i > $i).
% 29.69/17.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 29.69/17.46  tff(a_2_0_orders_2, type, a_2_0_orders_2: ($i * $i) > $i).
% 29.69/17.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 29.69/17.46  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 29.69/17.46  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 29.69/17.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 29.69/17.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 29.69/17.46  tff('#skF_5', type, '#skF_5': $i).
% 29.69/17.46  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 29.69/17.46  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 29.69/17.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 29.69/17.46  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 29.69/17.46  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 29.69/17.46  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 29.69/17.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 29.69/17.46  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 29.69/17.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 29.69/17.46  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 29.69/17.46  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 29.69/17.46  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 29.69/17.46  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 29.69/17.46  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 29.69/17.46  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 29.69/17.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 29.69/17.46  
% 29.69/17.48  tff(f_36, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 29.69/17.48  tff(f_38, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 29.69/17.48  tff(f_200, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k1_orders_2(A, k2_struct_0(A)) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_orders_2)).
% 29.69/17.48  tff(f_103, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 29.69/17.48  tff(f_79, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 29.69/17.48  tff(f_99, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_orders_2(A, B) = a_2_0_orders_2(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_orders_2)).
% 29.69/17.48  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 29.69/17.48  tff(f_71, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 29.69/17.48  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 29.69/17.48  tff(f_130, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_0_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, E, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_0_orders_2)).
% 29.69/17.48  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 29.69/17.48  tff(f_75, axiom, (![A]: (l1_struct_0(A) => (k1_struct_0(A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_struct_0)).
% 29.69/17.48  tff(f_186, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k1_orders_2(A, k1_struct_0(A)) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_orders_2)).
% 29.69/17.48  tff(f_40, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 29.69/17.48  tff(f_55, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 29.69/17.48  tff(f_50, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 29.69/17.48  tff(f_158, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => r3_orders_2(A, B, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r3_orders_2)).
% 29.69/17.48  tff(f_145, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 29.69/17.48  tff(f_173, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r1_orders_2(A, B, C) & r2_orders_2(A, C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_orders_2)).
% 29.69/17.48  tff(c_10, plain, (![A_7]: (k2_subset_1(A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_36])).
% 29.69/17.48  tff(c_12, plain, (![A_8]: (m1_subset_1(k2_subset_1(A_8), k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 29.69/17.48  tff(c_73, plain, (![A_8]: (m1_subset_1(A_8, k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 29.69/17.48  tff(c_72, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_200])).
% 29.69/17.48  tff(c_70, plain, (v3_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_200])).
% 29.69/17.48  tff(c_68, plain, (v4_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_200])).
% 29.69/17.48  tff(c_66, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_200])).
% 29.69/17.48  tff(c_64, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_200])).
% 29.69/17.48  tff(c_38, plain, (![A_33]: (l1_struct_0(A_33) | ~l1_orders_2(A_33))), inference(cnfTransformation, [status(thm)], [f_103])).
% 29.69/17.48  tff(c_102, plain, (![A_70]: (u1_struct_0(A_70)=k2_struct_0(A_70) | ~l1_struct_0(A_70))), inference(cnfTransformation, [status(thm)], [f_79])).
% 29.69/17.48  tff(c_112, plain, (![A_72]: (u1_struct_0(A_72)=k2_struct_0(A_72) | ~l1_orders_2(A_72))), inference(resolution, [status(thm)], [c_38, c_102])).
% 29.69/17.48  tff(c_116, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_64, c_112])).
% 29.69/17.48  tff(c_15302, plain, (![A_727, B_728]: (k1_orders_2(A_727, B_728)=a_2_0_orders_2(A_727, B_728) | ~m1_subset_1(B_728, k1_zfmisc_1(u1_struct_0(A_727))) | ~l1_orders_2(A_727) | ~v5_orders_2(A_727) | ~v4_orders_2(A_727) | ~v3_orders_2(A_727) | v2_struct_0(A_727))), inference(cnfTransformation, [status(thm)], [f_99])).
% 29.69/17.48  tff(c_15320, plain, (![B_728]: (k1_orders_2('#skF_5', B_728)=a_2_0_orders_2('#skF_5', B_728) | ~m1_subset_1(B_728, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_116, c_15302])).
% 29.69/17.48  tff(c_15334, plain, (![B_728]: (k1_orders_2('#skF_5', B_728)=a_2_0_orders_2('#skF_5', B_728) | ~m1_subset_1(B_728, k1_zfmisc_1(k2_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_15320])).
% 29.69/17.48  tff(c_15372, plain, (![B_732]: (k1_orders_2('#skF_5', B_732)=a_2_0_orders_2('#skF_5', B_732) | ~m1_subset_1(B_732, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_72, c_15334])).
% 29.69/17.48  tff(c_15401, plain, (k1_orders_2('#skF_5', k2_struct_0('#skF_5'))=a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_73, c_15372])).
% 29.69/17.48  tff(c_62, plain, (k1_orders_2('#skF_5', k2_struct_0('#skF_5'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_200])).
% 29.69/17.48  tff(c_15408, plain, (a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_15401, c_62])).
% 29.69/17.48  tff(c_129, plain, (![A_76, B_77]: (r1_tarski(A_76, B_77) | ~m1_subset_1(A_76, k1_zfmisc_1(B_77)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 29.69/17.48  tff(c_140, plain, (![A_8]: (r1_tarski(A_8, A_8))), inference(resolution, [status(thm)], [c_73, c_129])).
% 29.69/17.48  tff(c_24, plain, (![A_17]: (r2_hidden('#skF_2'(A_17), A_17) | k1_xboole_0=A_17)), inference(cnfTransformation, [status(thm)], [f_71])).
% 29.69/17.48  tff(c_177, plain, (![C_87, B_88, A_89]: (r2_hidden(C_87, B_88) | ~r2_hidden(C_87, A_89) | ~r1_tarski(A_89, B_88))), inference(cnfTransformation, [status(thm)], [f_32])).
% 29.69/17.48  tff(c_183, plain, (![A_17, B_88]: (r2_hidden('#skF_2'(A_17), B_88) | ~r1_tarski(A_17, B_88) | k1_xboole_0=A_17)), inference(resolution, [status(thm)], [c_24, c_177])).
% 29.69/17.48  tff(c_15849, plain, (![A_756, B_757, C_758]: ('#skF_3'(A_756, B_757, C_758)=A_756 | ~r2_hidden(A_756, a_2_0_orders_2(B_757, C_758)) | ~m1_subset_1(C_758, k1_zfmisc_1(u1_struct_0(B_757))) | ~l1_orders_2(B_757) | ~v5_orders_2(B_757) | ~v4_orders_2(B_757) | ~v3_orders_2(B_757) | v2_struct_0(B_757))), inference(cnfTransformation, [status(thm)], [f_130])).
% 29.69/17.48  tff(c_42374, plain, (![B_1592, C_1593]: ('#skF_3'('#skF_2'(a_2_0_orders_2(B_1592, C_1593)), B_1592, C_1593)='#skF_2'(a_2_0_orders_2(B_1592, C_1593)) | ~m1_subset_1(C_1593, k1_zfmisc_1(u1_struct_0(B_1592))) | ~l1_orders_2(B_1592) | ~v5_orders_2(B_1592) | ~v4_orders_2(B_1592) | ~v3_orders_2(B_1592) | v2_struct_0(B_1592) | a_2_0_orders_2(B_1592, C_1593)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_15849])).
% 29.69/17.48  tff(c_42405, plain, (![C_1593]: ('#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5', C_1593)), '#skF_5', C_1593)='#skF_2'(a_2_0_orders_2('#skF_5', C_1593)) | ~m1_subset_1(C_1593, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5') | a_2_0_orders_2('#skF_5', C_1593)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_116, c_42374])).
% 29.69/17.48  tff(c_42423, plain, (![C_1593]: ('#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5', C_1593)), '#skF_5', C_1593)='#skF_2'(a_2_0_orders_2('#skF_5', C_1593)) | ~m1_subset_1(C_1593, k1_zfmisc_1(k2_struct_0('#skF_5'))) | v2_struct_0('#skF_5') | a_2_0_orders_2('#skF_5', C_1593)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_42405])).
% 29.69/17.48  tff(c_42738, plain, (![C_1609]: ('#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5', C_1609)), '#skF_5', C_1609)='#skF_2'(a_2_0_orders_2('#skF_5', C_1609)) | ~m1_subset_1(C_1609, k1_zfmisc_1(k2_struct_0('#skF_5'))) | a_2_0_orders_2('#skF_5', C_1609)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_72, c_42423])).
% 29.69/17.48  tff(c_42768, plain, ('#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), '#skF_5', k2_struct_0('#skF_5'))='#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))) | a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_73, c_42738])).
% 29.69/17.48  tff(c_42785, plain, ('#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), '#skF_5', k2_struct_0('#skF_5'))='#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_15408, c_42768])).
% 29.69/17.48  tff(c_50, plain, (![A_34, B_35, C_36]: (m1_subset_1('#skF_3'(A_34, B_35, C_36), u1_struct_0(B_35)) | ~r2_hidden(A_34, a_2_0_orders_2(B_35, C_36)) | ~m1_subset_1(C_36, k1_zfmisc_1(u1_struct_0(B_35))) | ~l1_orders_2(B_35) | ~v5_orders_2(B_35) | ~v4_orders_2(B_35) | ~v3_orders_2(B_35) | v2_struct_0(B_35))), inference(cnfTransformation, [status(thm)], [f_130])).
% 29.69/17.48  tff(c_44041, plain, (m1_subset_1('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), u1_struct_0('#skF_5')) | ~r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))) | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_42785, c_50])).
% 29.69/17.48  tff(c_44055, plain, (m1_subset_1('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), k2_struct_0('#skF_5')) | ~r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_73, c_116, c_116, c_44041])).
% 29.69/17.48  tff(c_44056, plain, (m1_subset_1('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), k2_struct_0('#skF_5')) | ~r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_72, c_44055])).
% 29.69/17.48  tff(c_44161, plain, (~r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')))), inference(splitLeft, [status(thm)], [c_44056])).
% 29.69/17.48  tff(c_44164, plain, (~r1_tarski(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')), a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))) | a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_183, c_44161])).
% 29.69/17.48  tff(c_44170, plain, (a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_140, c_44164])).
% 29.69/17.48  tff(c_44172, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15408, c_44170])).
% 29.69/17.48  tff(c_44173, plain, (m1_subset_1('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), k2_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_44056])).
% 29.69/17.48  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 29.69/17.48  tff(c_87, plain, (![A_66]: (k1_struct_0(A_66)=k1_xboole_0 | ~l1_struct_0(A_66))), inference(cnfTransformation, [status(thm)], [f_75])).
% 29.69/17.48  tff(c_92, plain, (![A_67]: (k1_struct_0(A_67)=k1_xboole_0 | ~l1_orders_2(A_67))), inference(resolution, [status(thm)], [c_38, c_87])).
% 29.69/17.48  tff(c_96, plain, (k1_struct_0('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_64, c_92])).
% 29.69/17.48  tff(c_288, plain, (![A_111]: (k1_orders_2(A_111, k1_struct_0(A_111))=u1_struct_0(A_111) | ~l1_orders_2(A_111) | ~v5_orders_2(A_111) | ~v4_orders_2(A_111) | ~v3_orders_2(A_111) | v2_struct_0(A_111))), inference(cnfTransformation, [status(thm)], [f_186])).
% 29.69/17.48  tff(c_297, plain, (k1_orders_2('#skF_5', k1_xboole_0)=u1_struct_0('#skF_5') | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_96, c_288])).
% 29.69/17.48  tff(c_301, plain, (k1_orders_2('#skF_5', k1_xboole_0)=k2_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_116, c_297])).
% 29.69/17.48  tff(c_302, plain, (k1_orders_2('#skF_5', k1_xboole_0)=k2_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_72, c_301])).
% 29.69/17.48  tff(c_14, plain, (![A_9]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 29.69/17.48  tff(c_15396, plain, (k1_orders_2('#skF_5', k1_xboole_0)=a_2_0_orders_2('#skF_5', k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_15372])).
% 29.69/17.48  tff(c_15403, plain, (a_2_0_orders_2('#skF_5', k1_xboole_0)=k2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_302, c_15396])).
% 29.69/17.48  tff(c_16333, plain, (![D_782, B_783, C_784]: (r2_hidden('#skF_4'(D_782, B_783, C_784, D_782), C_784) | r2_hidden(D_782, a_2_0_orders_2(B_783, C_784)) | ~m1_subset_1(D_782, u1_struct_0(B_783)) | ~m1_subset_1(C_784, k1_zfmisc_1(u1_struct_0(B_783))) | ~l1_orders_2(B_783) | ~v5_orders_2(B_783) | ~v4_orders_2(B_783) | ~v3_orders_2(B_783) | v2_struct_0(B_783))), inference(cnfTransformation, [status(thm)], [f_130])).
% 29.69/17.48  tff(c_16352, plain, (![D_782, C_784]: (r2_hidden('#skF_4'(D_782, '#skF_5', C_784, D_782), C_784) | r2_hidden(D_782, a_2_0_orders_2('#skF_5', C_784)) | ~m1_subset_1(D_782, u1_struct_0('#skF_5')) | ~m1_subset_1(C_784, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_116, c_16333])).
% 29.69/17.48  tff(c_16366, plain, (![D_782, C_784]: (r2_hidden('#skF_4'(D_782, '#skF_5', C_784, D_782), C_784) | r2_hidden(D_782, a_2_0_orders_2('#skF_5', C_784)) | ~m1_subset_1(D_782, k2_struct_0('#skF_5')) | ~m1_subset_1(C_784, k1_zfmisc_1(k2_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_116, c_16352])).
% 29.69/17.48  tff(c_16450, plain, (![D_794, C_795]: (r2_hidden('#skF_4'(D_794, '#skF_5', C_795, D_794), C_795) | r2_hidden(D_794, a_2_0_orders_2('#skF_5', C_795)) | ~m1_subset_1(D_794, k2_struct_0('#skF_5')) | ~m1_subset_1(C_795, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_72, c_16366])).
% 29.69/17.48  tff(c_16471, plain, (![D_794]: (r2_hidden('#skF_4'(D_794, '#skF_5', k1_xboole_0, D_794), k1_xboole_0) | r2_hidden(D_794, a_2_0_orders_2('#skF_5', k1_xboole_0)) | ~m1_subset_1(D_794, k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_14, c_16450])).
% 29.69/17.48  tff(c_41649, plain, (![D_1570]: (r2_hidden('#skF_4'(D_1570, '#skF_5', k1_xboole_0, D_1570), k1_xboole_0) | r2_hidden(D_1570, k2_struct_0('#skF_5')) | ~m1_subset_1(D_1570, k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_15403, c_16471])).
% 29.69/17.48  tff(c_22, plain, (![B_16, A_15]: (~r1_tarski(B_16, A_15) | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_55])).
% 29.69/17.48  tff(c_41665, plain, (![D_1570]: (~r1_tarski(k1_xboole_0, '#skF_4'(D_1570, '#skF_5', k1_xboole_0, D_1570)) | r2_hidden(D_1570, k2_struct_0('#skF_5')) | ~m1_subset_1(D_1570, k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_41649, c_22])).
% 29.69/17.48  tff(c_41680, plain, (![D_1570]: (r2_hidden(D_1570, k2_struct_0('#skF_5')) | ~m1_subset_1(D_1570, k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_41665])).
% 29.69/17.48  tff(c_41768, plain, (![D_1573]: (r2_hidden(D_1573, k2_struct_0('#skF_5')) | ~m1_subset_1(D_1573, k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_41665])).
% 29.69/17.48  tff(c_15854, plain, (![A_756]: ('#skF_3'(A_756, '#skF_5', k1_xboole_0)=A_756 | ~r2_hidden(A_756, k2_struct_0('#skF_5')) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_15403, c_15849])).
% 29.69/17.48  tff(c_15866, plain, (![A_756]: ('#skF_3'(A_756, '#skF_5', k1_xboole_0)=A_756 | ~r2_hidden(A_756, k2_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_14, c_116, c_15854])).
% 29.69/17.48  tff(c_15867, plain, (![A_756]: ('#skF_3'(A_756, '#skF_5', k1_xboole_0)=A_756 | ~r2_hidden(A_756, k2_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_72, c_15866])).
% 29.69/17.48  tff(c_41797, plain, (![D_1573]: ('#skF_3'(D_1573, '#skF_5', k1_xboole_0)=D_1573 | ~m1_subset_1(D_1573, k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_41768, c_15867])).
% 29.69/17.48  tff(c_44182, plain, ('#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), '#skF_5', k1_xboole_0)='#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_44173, c_41797])).
% 29.69/17.48  tff(c_18, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 29.69/17.48  tff(c_17280, plain, (![B_838, E_839, A_840, C_841]: (r2_orders_2(B_838, E_839, '#skF_3'(A_840, B_838, C_841)) | ~r2_hidden(E_839, C_841) | ~m1_subset_1(E_839, u1_struct_0(B_838)) | ~r2_hidden(A_840, a_2_0_orders_2(B_838, C_841)) | ~m1_subset_1(C_841, k1_zfmisc_1(u1_struct_0(B_838))) | ~l1_orders_2(B_838) | ~v5_orders_2(B_838) | ~v4_orders_2(B_838) | ~v3_orders_2(B_838) | v2_struct_0(B_838))), inference(cnfTransformation, [status(thm)], [f_130])).
% 29.69/17.48  tff(c_17311, plain, (![B_838, E_839, A_840, A_10]: (r2_orders_2(B_838, E_839, '#skF_3'(A_840, B_838, A_10)) | ~r2_hidden(E_839, A_10) | ~m1_subset_1(E_839, u1_struct_0(B_838)) | ~r2_hidden(A_840, a_2_0_orders_2(B_838, A_10)) | ~l1_orders_2(B_838) | ~v5_orders_2(B_838) | ~v4_orders_2(B_838) | ~v3_orders_2(B_838) | v2_struct_0(B_838) | ~r1_tarski(A_10, u1_struct_0(B_838)))), inference(resolution, [status(thm)], [c_18, c_17280])).
% 29.69/17.48  tff(c_44430, plain, (![E_839]: (r2_orders_2('#skF_5', E_839, '#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')))) | ~r2_hidden(E_839, k1_xboole_0) | ~m1_subset_1(E_839, u1_struct_0('#skF_5')) | ~r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), a_2_0_orders_2('#skF_5', k1_xboole_0)) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5') | ~r1_tarski(k1_xboole_0, u1_struct_0('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_44182, c_17311])).
% 29.69/17.48  tff(c_44443, plain, (![E_839]: (r2_orders_2('#skF_5', E_839, '#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')))) | ~r2_hidden(E_839, k1_xboole_0) | ~m1_subset_1(E_839, k2_struct_0('#skF_5')) | ~r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), k2_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_116, c_70, c_68, c_66, c_64, c_15403, c_116, c_44430])).
% 29.69/17.48  tff(c_44444, plain, (![E_839]: (r2_orders_2('#skF_5', E_839, '#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')))) | ~r2_hidden(E_839, k1_xboole_0) | ~m1_subset_1(E_839, k2_struct_0('#skF_5')) | ~r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), k2_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_72, c_44443])).
% 29.69/17.48  tff(c_44601, plain, (~r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), k2_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_44444])).
% 29.69/17.48  tff(c_44607, plain, (~m1_subset_1('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_41680, c_44601])).
% 29.69/17.48  tff(c_44615, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44173, c_44607])).
% 29.69/17.48  tff(c_44617, plain, (r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), k2_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_44444])).
% 29.69/17.48  tff(c_237, plain, (![A_103, C_104, B_105]: (m1_subset_1(A_103, C_104) | ~m1_subset_1(B_105, k1_zfmisc_1(C_104)) | ~r2_hidden(A_103, B_105))), inference(cnfTransformation, [status(thm)], [f_50])).
% 29.69/17.48  tff(c_250, plain, (![A_106, A_107]: (m1_subset_1(A_106, A_107) | ~r2_hidden(A_106, A_107))), inference(resolution, [status(thm)], [c_73, c_237])).
% 29.69/17.48  tff(c_262, plain, (![A_17]: (m1_subset_1('#skF_2'(A_17), A_17) | k1_xboole_0=A_17)), inference(resolution, [status(thm)], [c_24, c_250])).
% 29.69/17.48  tff(c_15084, plain, (![A_708, B_709, C_710]: (r3_orders_2(A_708, B_709, B_709) | ~m1_subset_1(C_710, u1_struct_0(A_708)) | ~m1_subset_1(B_709, u1_struct_0(A_708)) | ~l1_orders_2(A_708) | ~v3_orders_2(A_708) | v2_struct_0(A_708))), inference(cnfTransformation, [status(thm)], [f_158])).
% 29.69/17.48  tff(c_15092, plain, (![B_709, C_710]: (r3_orders_2('#skF_5', B_709, B_709) | ~m1_subset_1(C_710, k2_struct_0('#skF_5')) | ~m1_subset_1(B_709, u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_116, c_15084])).
% 29.69/17.48  tff(c_15096, plain, (![B_709, C_710]: (r3_orders_2('#skF_5', B_709, B_709) | ~m1_subset_1(C_710, k2_struct_0('#skF_5')) | ~m1_subset_1(B_709, k2_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_64, c_116, c_15092])).
% 29.69/17.48  tff(c_15097, plain, (![B_709, C_710]: (r3_orders_2('#skF_5', B_709, B_709) | ~m1_subset_1(C_710, k2_struct_0('#skF_5')) | ~m1_subset_1(B_709, k2_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_72, c_15096])).
% 29.69/17.48  tff(c_15140, plain, (![C_712]: (~m1_subset_1(C_712, k2_struct_0('#skF_5')))), inference(splitLeft, [status(thm)], [c_15097])).
% 29.69/17.48  tff(c_15150, plain, (k2_struct_0('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_262, c_15140])).
% 29.69/17.48  tff(c_15152, plain, (k1_orders_2('#skF_5', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_15150, c_302])).
% 29.69/17.48  tff(c_15154, plain, (k1_orders_2('#skF_5', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_15150, c_62])).
% 29.69/17.48  tff(c_15204, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15152, c_15154])).
% 29.69/17.48  tff(c_15205, plain, (![B_709]: (r3_orders_2('#skF_5', B_709, B_709) | ~m1_subset_1(B_709, k2_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_15097])).
% 29.69/17.48  tff(c_44184, plain, (r3_orders_2('#skF_5', '#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), '#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_44173, c_15205])).
% 29.69/17.48  tff(c_54, plain, (![A_47, B_48, C_49]: (r1_orders_2(A_47, B_48, C_49) | ~r3_orders_2(A_47, B_48, C_49) | ~m1_subset_1(C_49, u1_struct_0(A_47)) | ~m1_subset_1(B_48, u1_struct_0(A_47)) | ~l1_orders_2(A_47) | ~v3_orders_2(A_47) | v2_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_145])).
% 29.69/17.48  tff(c_44269, plain, (r1_orders_2('#skF_5', '#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), '#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')))) | ~m1_subset_1('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_44184, c_54])).
% 29.69/17.48  tff(c_44272, plain, (r1_orders_2('#skF_5', '#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), '#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_64, c_44173, c_116, c_44269])).
% 29.69/17.48  tff(c_44273, plain, (r1_orders_2('#skF_5', '#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), '#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_72, c_44272])).
% 29.69/17.48  tff(c_44174, plain, (r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_44056])).
% 29.69/17.48  tff(c_42421, plain, (![B_1592, A_10]: ('#skF_3'('#skF_2'(a_2_0_orders_2(B_1592, A_10)), B_1592, A_10)='#skF_2'(a_2_0_orders_2(B_1592, A_10)) | ~l1_orders_2(B_1592) | ~v5_orders_2(B_1592) | ~v4_orders_2(B_1592) | ~v3_orders_2(B_1592) | v2_struct_0(B_1592) | a_2_0_orders_2(B_1592, A_10)=k1_xboole_0 | ~r1_tarski(A_10, u1_struct_0(B_1592)))), inference(resolution, [status(thm)], [c_18, c_42374])).
% 29.69/17.48  tff(c_43514, plain, (![B_1625, E_1626, A_1627]: (r2_orders_2(B_1625, E_1626, '#skF_3'(A_1627, B_1625, u1_struct_0(B_1625))) | ~r2_hidden(E_1626, u1_struct_0(B_1625)) | ~m1_subset_1(E_1626, u1_struct_0(B_1625)) | ~r2_hidden(A_1627, a_2_0_orders_2(B_1625, u1_struct_0(B_1625))) | ~l1_orders_2(B_1625) | ~v5_orders_2(B_1625) | ~v4_orders_2(B_1625) | ~v3_orders_2(B_1625) | v2_struct_0(B_1625))), inference(resolution, [status(thm)], [c_73, c_17280])).
% 29.69/17.48  tff(c_58, plain, (![A_53, C_59, B_57]: (~r2_orders_2(A_53, C_59, B_57) | ~r1_orders_2(A_53, B_57, C_59) | ~m1_subset_1(C_59, u1_struct_0(A_53)) | ~m1_subset_1(B_57, u1_struct_0(A_53)) | ~l1_orders_2(A_53) | ~v5_orders_2(A_53))), inference(cnfTransformation, [status(thm)], [f_173])).
% 29.69/17.48  tff(c_86463, plain, (![B_2200, A_2201, E_2202]: (~r1_orders_2(B_2200, '#skF_3'(A_2201, B_2200, u1_struct_0(B_2200)), E_2202) | ~m1_subset_1('#skF_3'(A_2201, B_2200, u1_struct_0(B_2200)), u1_struct_0(B_2200)) | ~r2_hidden(E_2202, u1_struct_0(B_2200)) | ~m1_subset_1(E_2202, u1_struct_0(B_2200)) | ~r2_hidden(A_2201, a_2_0_orders_2(B_2200, u1_struct_0(B_2200))) | ~l1_orders_2(B_2200) | ~v5_orders_2(B_2200) | ~v4_orders_2(B_2200) | ~v3_orders_2(B_2200) | v2_struct_0(B_2200))), inference(resolution, [status(thm)], [c_43514, c_58])).
% 29.69/17.48  tff(c_86475, plain, (![A_2201, E_2202]: (~r1_orders_2('#skF_5', '#skF_3'(A_2201, '#skF_5', k2_struct_0('#skF_5')), E_2202) | ~m1_subset_1('#skF_3'(A_2201, '#skF_5', u1_struct_0('#skF_5')), u1_struct_0('#skF_5')) | ~r2_hidden(E_2202, u1_struct_0('#skF_5')) | ~m1_subset_1(E_2202, u1_struct_0('#skF_5')) | ~r2_hidden(A_2201, a_2_0_orders_2('#skF_5', u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_116, c_86463])).
% 29.69/17.48  tff(c_86481, plain, (![A_2201, E_2202]: (~r1_orders_2('#skF_5', '#skF_3'(A_2201, '#skF_5', k2_struct_0('#skF_5')), E_2202) | ~m1_subset_1('#skF_3'(A_2201, '#skF_5', k2_struct_0('#skF_5')), k2_struct_0('#skF_5')) | ~r2_hidden(E_2202, k2_struct_0('#skF_5')) | ~m1_subset_1(E_2202, k2_struct_0('#skF_5')) | ~r2_hidden(A_2201, a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_116, c_116, c_116, c_116, c_116, c_86475])).
% 29.69/17.48  tff(c_86733, plain, (![A_2206, E_2207]: (~r1_orders_2('#skF_5', '#skF_3'(A_2206, '#skF_5', k2_struct_0('#skF_5')), E_2207) | ~m1_subset_1('#skF_3'(A_2206, '#skF_5', k2_struct_0('#skF_5')), k2_struct_0('#skF_5')) | ~r2_hidden(E_2207, k2_struct_0('#skF_5')) | ~m1_subset_1(E_2207, k2_struct_0('#skF_5')) | ~r2_hidden(A_2206, a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_72, c_86481])).
% 29.69/17.48  tff(c_86747, plain, (![E_2207]: (~r1_orders_2('#skF_5', '#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), E_2207) | ~m1_subset_1('#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), '#skF_5', k2_struct_0('#skF_5')), k2_struct_0('#skF_5')) | ~r2_hidden(E_2207, k2_struct_0('#skF_5')) | ~m1_subset_1(E_2207, k2_struct_0('#skF_5')) | ~r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5') | a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))=k1_xboole_0 | ~r1_tarski(k2_struct_0('#skF_5'), u1_struct_0('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_42421, c_86733])).
% 29.69/17.48  tff(c_86760, plain, (![E_2207]: (~r1_orders_2('#skF_5', '#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), E_2207) | ~r2_hidden(E_2207, k2_struct_0('#skF_5')) | ~m1_subset_1(E_2207, k2_struct_0('#skF_5')) | v2_struct_0('#skF_5') | a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_140, c_116, c_70, c_68, c_66, c_64, c_44174, c_44173, c_42785, c_86747])).
% 29.69/17.48  tff(c_87400, plain, (![E_2222]: (~r1_orders_2('#skF_5', '#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), E_2222) | ~r2_hidden(E_2222, k2_struct_0('#skF_5')) | ~m1_subset_1(E_2222, k2_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_15408, c_72, c_86760])).
% 29.69/17.48  tff(c_87403, plain, (~r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), k2_struct_0('#skF_5')) | ~m1_subset_1('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_44273, c_87400])).
% 29.69/17.48  tff(c_87411, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44173, c_44617, c_87403])).
% 29.69/17.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 29.69/17.48  
% 29.69/17.48  Inference rules
% 29.69/17.48  ----------------------
% 29.69/17.48  #Ref     : 0
% 29.69/17.48  #Sup     : 20179
% 29.69/17.48  #Fact    : 6
% 29.69/17.48  #Define  : 0
% 29.69/17.48  #Split   : 68
% 29.69/17.48  #Chain   : 0
% 29.69/17.48  #Close   : 0
% 29.69/17.48  
% 29.69/17.48  Ordering : KBO
% 29.69/17.48  
% 29.69/17.48  Simplification rules
% 29.69/17.48  ----------------------
% 29.69/17.48  #Subsume      : 9518
% 29.69/17.48  #Demod        : 10384
% 29.69/17.48  #Tautology    : 3325
% 29.69/17.48  #SimpNegUnit  : 2619
% 29.69/17.48  #BackRed      : 119
% 29.69/17.48  
% 29.69/17.48  #Partial instantiations: 0
% 29.69/17.48  #Strategies tried      : 1
% 29.69/17.48  
% 29.69/17.48  Timing (in seconds)
% 29.69/17.48  ----------------------
% 29.69/17.48  Preprocessing        : 0.59
% 29.69/17.48  Parsing              : 0.31
% 29.69/17.48  CNF conversion       : 0.05
% 29.69/17.48  Main loop            : 16.07
% 29.69/17.48  Inferencing          : 3.18
% 29.69/17.48  Reduction            : 4.97
% 29.69/17.48  Demodulation         : 3.37
% 29.69/17.48  BG Simplification    : 0.29
% 29.69/17.48  Subsumption          : 6.66
% 29.69/17.48  Abstraction          : 0.49
% 29.69/17.48  MUC search           : 0.00
% 29.69/17.49  Cooper               : 0.00
% 29.69/17.49  Total                : 16.72
% 29.69/17.49  Index Insertion      : 0.00
% 29.69/17.49  Index Deletion       : 0.00
% 29.69/17.49  Index Matching       : 0.00
% 29.69/17.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
