%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:50 EST 2020

% Result     : Theorem 3.10s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :  185 (1470 expanded)
%              Number of leaves         :   24 ( 572 expanded)
%              Depth                    :   15
%              Number of atoms          :  599 (8197 expanded)
%              Number of equality atoms :  113 (1088 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > m1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_orders_2,type,(
    k3_orders_2: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(m1_orders_2,type,(
    m1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_132,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ ( B != k1_xboole_0
                    & m1_orders_2(B,A,C)
                    & m1_orders_2(C,A,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_orders_2)).

tff(f_60,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( B != k1_xboole_0
                 => ( m1_orders_2(C,A,B)
                  <=> ? [D] :
                        ( m1_subset_1(D,u1_struct_0(A))
                        & r2_hidden(D,B)
                        & C = k3_orders_2(A,B,D) ) ) )
                & ( B = k1_xboole_0
                 => ( m1_orders_2(C,A,B)
                  <=> C = k1_xboole_0 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_orders_2)).

tff(f_106,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ~ r2_hidden(B,k3_orders_2(A,C,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_orders_2)).

tff(f_86,axiom,(
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
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                 => ( r2_hidden(B,k3_orders_2(A,D,C))
                  <=> ( r2_orders_2(A,B,C)
                      & r2_hidden(B,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).

tff(c_24,plain,(
    m1_orders_2('#skF_3','#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_38,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_36,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_34,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_32,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_274,plain,(
    ! [A_89,B_90,C_91] :
      ( r2_hidden('#skF_1'(A_89,B_90,C_91),B_90)
      | ~ m1_orders_2(C_91,A_89,B_90)
      | k1_xboole_0 = B_90
      | ~ m1_subset_1(C_91,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ m1_subset_1(B_90,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ l1_orders_2(A_89)
      | ~ v5_orders_2(A_89)
      | ~ v4_orders_2(A_89)
      | ~ v3_orders_2(A_89)
      | v2_struct_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_278,plain,(
    ! [B_90] :
      ( r2_hidden('#skF_1'('#skF_2',B_90,'#skF_4'),B_90)
      | ~ m1_orders_2('#skF_4','#skF_2',B_90)
      | k1_xboole_0 = B_90
      | ~ m1_subset_1(B_90,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_274])).

tff(c_287,plain,(
    ! [B_90] :
      ( r2_hidden('#skF_1'('#skF_2',B_90,'#skF_4'),B_90)
      | ~ m1_orders_2('#skF_4','#skF_2',B_90)
      | k1_xboole_0 = B_90
      | ~ m1_subset_1(B_90,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_278])).

tff(c_293,plain,(
    ! [B_92] :
      ( r2_hidden('#skF_1'('#skF_2',B_92,'#skF_4'),B_92)
      | ~ m1_orders_2('#skF_4','#skF_2',B_92)
      | k1_xboole_0 = B_92
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_287])).

tff(c_301,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_4','#skF_4'),'#skF_4')
    | ~ m1_orders_2('#skF_4','#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_28,c_293])).

tff(c_307,plain,(
    ~ m1_orders_2('#skF_4','#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_301])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_280,plain,(
    ! [B_90] :
      ( r2_hidden('#skF_1'('#skF_2',B_90,'#skF_3'),B_90)
      | ~ m1_orders_2('#skF_3','#skF_2',B_90)
      | k1_xboole_0 = B_90
      | ~ m1_subset_1(B_90,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_30,c_274])).

tff(c_291,plain,(
    ! [B_90] :
      ( r2_hidden('#skF_1'('#skF_2',B_90,'#skF_3'),B_90)
      | ~ m1_orders_2('#skF_3','#skF_2',B_90)
      | k1_xboole_0 = B_90
      | ~ m1_subset_1(B_90,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_280])).

tff(c_308,plain,(
    ! [B_97] :
      ( r2_hidden('#skF_1'('#skF_2',B_97,'#skF_3'),B_97)
      | ~ m1_orders_2('#skF_3','#skF_2',B_97)
      | k1_xboole_0 = B_97
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_291])).

tff(c_312,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_4','#skF_3'),'#skF_4')
    | ~ m1_orders_2('#skF_3','#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_28,c_308])).

tff(c_318,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_4','#skF_3'),'#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_312])).

tff(c_322,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_318])).

tff(c_57,plain,(
    ! [A_55,B_56,C_57] :
      ( r2_hidden('#skF_1'(A_55,B_56,C_57),B_56)
      | ~ m1_orders_2(C_57,A_55,B_56)
      | k1_xboole_0 = B_56
      | ~ m1_subset_1(C_57,k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ l1_orders_2(A_55)
      | ~ v5_orders_2(A_55)
      | ~ v4_orders_2(A_55)
      | ~ v3_orders_2(A_55)
      | v2_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_61,plain,(
    ! [B_56] :
      ( r2_hidden('#skF_1'('#skF_2',B_56,'#skF_3'),B_56)
      | ~ m1_orders_2('#skF_3','#skF_2',B_56)
      | k1_xboole_0 = B_56
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_30,c_57])).

tff(c_68,plain,(
    ! [B_56] :
      ( r2_hidden('#skF_1'('#skF_2',B_56,'#skF_3'),B_56)
      | ~ m1_orders_2('#skF_3','#skF_2',B_56)
      | k1_xboole_0 = B_56
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_61])).

tff(c_81,plain,(
    ! [B_59] :
      ( r2_hidden('#skF_1'('#skF_2',B_59,'#skF_3'),B_59)
      | ~ m1_orders_2('#skF_3','#skF_2',B_59)
      | k1_xboole_0 = B_59
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_68])).

tff(c_83,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_4','#skF_3'),'#skF_4')
    | ~ m1_orders_2('#skF_3','#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_28,c_81])).

tff(c_88,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_4','#skF_3'),'#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_83])).

tff(c_92,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_43,plain,(
    ! [C_53,A_54] :
      ( k1_xboole_0 = C_53
      | ~ m1_orders_2(C_53,A_54,k1_xboole_0)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ l1_orders_2(A_54)
      | ~ v5_orders_2(A_54)
      | ~ v4_orders_2(A_54)
      | ~ v3_orders_2(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_47,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ m1_orders_2('#skF_3','#skF_2',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_43])).

tff(c_54,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ m1_orders_2('#skF_3','#skF_2',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_47])).

tff(c_55,plain,
    ( ~ m1_orders_2('#skF_3','#skF_2',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_26,c_54])).

tff(c_56,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_55])).

tff(c_96,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_56])).

tff(c_102,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_96])).

tff(c_104,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_12,plain,(
    ! [A_1,B_13,C_19] :
      ( m1_subset_1('#skF_1'(A_1,B_13,C_19),u1_struct_0(A_1))
      | ~ m1_orders_2(C_19,A_1,B_13)
      | k1_xboole_0 = B_13
      | ~ m1_subset_1(C_19,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_orders_2(A_1)
      | ~ v5_orders_2(A_1)
      | ~ v4_orders_2(A_1)
      | ~ v3_orders_2(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_109,plain,(
    ! [A_71,B_72,C_73] :
      ( k3_orders_2(A_71,B_72,'#skF_1'(A_71,B_72,C_73)) = C_73
      | ~ m1_orders_2(C_73,A_71,B_72)
      | k1_xboole_0 = B_72
      | ~ m1_subset_1(C_73,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_orders_2(A_71)
      | ~ v5_orders_2(A_71)
      | ~ v4_orders_2(A_71)
      | ~ v3_orders_2(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_113,plain,(
    ! [B_72] :
      ( k3_orders_2('#skF_2',B_72,'#skF_1'('#skF_2',B_72,'#skF_3')) = '#skF_3'
      | ~ m1_orders_2('#skF_3','#skF_2',B_72)
      | k1_xboole_0 = B_72
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_30,c_109])).

tff(c_120,plain,(
    ! [B_72] :
      ( k3_orders_2('#skF_2',B_72,'#skF_1'('#skF_2',B_72,'#skF_3')) = '#skF_3'
      | ~ m1_orders_2('#skF_3','#skF_2',B_72)
      | k1_xboole_0 = B_72
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_113])).

tff(c_192,plain,(
    ! [B_80] :
      ( k3_orders_2('#skF_2',B_80,'#skF_1'('#skF_2',B_80,'#skF_3')) = '#skF_3'
      | ~ m1_orders_2('#skF_3','#skF_2',B_80)
      | k1_xboole_0 = B_80
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_120])).

tff(c_194,plain,
    ( k3_orders_2('#skF_2','#skF_4','#skF_1'('#skF_2','#skF_4','#skF_3')) = '#skF_3'
    | ~ m1_orders_2('#skF_3','#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_28,c_192])).

tff(c_199,plain,
    ( k3_orders_2('#skF_2','#skF_4','#skF_1'('#skF_2','#skF_4','#skF_3')) = '#skF_3'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_194])).

tff(c_200,plain,(
    k3_orders_2('#skF_2','#skF_4','#skF_1'('#skF_2','#skF_4','#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_199])).

tff(c_20,plain,(
    ! [B_42,A_38,C_44] :
      ( ~ r2_hidden(B_42,k3_orders_2(A_38,C_44,B_42))
      | ~ m1_subset_1(C_44,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ m1_subset_1(B_42,u1_struct_0(A_38))
      | ~ l1_orders_2(A_38)
      | ~ v5_orders_2(A_38)
      | ~ v4_orders_2(A_38)
      | ~ v3_orders_2(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_209,plain,
    ( ~ r2_hidden('#skF_1'('#skF_2','#skF_4','#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_20])).

tff(c_219,plain,
    ( ~ r2_hidden('#skF_1'('#skF_2','#skF_4','#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_28,c_209])).

tff(c_220,plain,
    ( ~ r2_hidden('#skF_1'('#skF_2','#skF_4','#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_219])).

tff(c_222,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_220])).

tff(c_225,plain,
    ( ~ m1_orders_2('#skF_3','#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_222])).

tff(c_228,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_28,c_30,c_24,c_225])).

tff(c_230,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_104,c_228])).

tff(c_231,plain,(
    ~ r2_hidden('#skF_1'('#skF_2','#skF_4','#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_220])).

tff(c_103,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_4','#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_232,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_220])).

tff(c_22,plain,(
    m1_orders_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_111,plain,(
    ! [B_72] :
      ( k3_orders_2('#skF_2',B_72,'#skF_1'('#skF_2',B_72,'#skF_4')) = '#skF_4'
      | ~ m1_orders_2('#skF_4','#skF_2',B_72)
      | k1_xboole_0 = B_72
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_109])).

tff(c_116,plain,(
    ! [B_72] :
      ( k3_orders_2('#skF_2',B_72,'#skF_1'('#skF_2',B_72,'#skF_4')) = '#skF_4'
      | ~ m1_orders_2('#skF_4','#skF_2',B_72)
      | k1_xboole_0 = B_72
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_111])).

tff(c_122,plain,(
    ! [B_74] :
      ( k3_orders_2('#skF_2',B_74,'#skF_1'('#skF_2',B_74,'#skF_4')) = '#skF_4'
      | ~ m1_orders_2('#skF_4','#skF_2',B_74)
      | k1_xboole_0 = B_74
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_116])).

tff(c_126,plain,
    ( k3_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3','#skF_4')) = '#skF_4'
    | ~ m1_orders_2('#skF_4','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_30,c_122])).

tff(c_131,plain,
    ( k3_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3','#skF_4')) = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_126])).

tff(c_132,plain,(
    k3_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3','#skF_4')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_131])).

tff(c_139,plain,
    ( ~ r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_20])).

tff(c_149,plain,
    ( ~ r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_30,c_139])).

tff(c_150,plain,
    ( ~ r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_149])).

tff(c_152,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_150])).

tff(c_168,plain,
    ( ~ m1_orders_2('#skF_4','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_152])).

tff(c_171,plain,
    ( k1_xboole_0 = '#skF_3'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_30,c_28,c_22,c_168])).

tff(c_173,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_26,c_171])).

tff(c_175,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_16,plain,(
    ! [B_31,D_37,A_23,C_35] :
      ( r2_hidden(B_31,D_37)
      | ~ r2_hidden(B_31,k3_orders_2(A_23,D_37,C_35))
      | ~ m1_subset_1(D_37,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ m1_subset_1(C_35,u1_struct_0(A_23))
      | ~ m1_subset_1(B_31,u1_struct_0(A_23))
      | ~ l1_orders_2(A_23)
      | ~ v5_orders_2(A_23)
      | ~ v4_orders_2(A_23)
      | ~ v3_orders_2(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_137,plain,(
    ! [B_31] :
      ( r2_hidden(B_31,'#skF_3')
      | ~ r2_hidden(B_31,'#skF_4')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_31,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_16])).

tff(c_146,plain,(
    ! [B_31] :
      ( r2_hidden(B_31,'#skF_3')
      | ~ r2_hidden(B_31,'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_31,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_30,c_137])).

tff(c_147,plain,(
    ! [B_31] :
      ( r2_hidden(B_31,'#skF_3')
      | ~ r2_hidden(B_31,'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_31,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_146])).

tff(c_177,plain,(
    ! [B_31] :
      ( r2_hidden(B_31,'#skF_3')
      | ~ r2_hidden(B_31,'#skF_4')
      | ~ m1_subset_1(B_31,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_147])).

tff(c_248,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_4','#skF_3'),'#skF_3')
    | ~ r2_hidden('#skF_1'('#skF_2','#skF_4','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_232,c_177])).

tff(c_251,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_4','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_248])).

tff(c_253,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_231,c_251])).

tff(c_255,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_55])).

tff(c_2,plain,(
    ! [A_1] :
      ( m1_orders_2(k1_xboole_0,A_1,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_orders_2(A_1)
      | ~ v5_orders_2(A_1)
      | ~ v4_orders_2(A_1)
      | ~ v3_orders_2(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_260,plain,
    ( m1_orders_2(k1_xboole_0,'#skF_2',k1_xboole_0)
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_255,c_2])).

tff(c_268,plain,
    ( m1_orders_2(k1_xboole_0,'#skF_2',k1_xboole_0)
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_260])).

tff(c_269,plain,(
    m1_orders_2(k1_xboole_0,'#skF_2',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_268])).

tff(c_327,plain,(
    m1_orders_2('#skF_4','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_322,c_269])).

tff(c_334,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_307,c_327])).

tff(c_336,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_318])).

tff(c_358,plain,(
    ! [A_102,B_103,C_104] :
      ( k3_orders_2(A_102,B_103,'#skF_1'(A_102,B_103,C_104)) = C_104
      | ~ m1_orders_2(C_104,A_102,B_103)
      | k1_xboole_0 = B_103
      | ~ m1_subset_1(C_104,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_orders_2(A_102)
      | ~ v5_orders_2(A_102)
      | ~ v4_orders_2(A_102)
      | ~ v3_orders_2(A_102)
      | v2_struct_0(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_364,plain,(
    ! [B_103] :
      ( k3_orders_2('#skF_2',B_103,'#skF_1'('#skF_2',B_103,'#skF_3')) = '#skF_3'
      | ~ m1_orders_2('#skF_3','#skF_2',B_103)
      | k1_xboole_0 = B_103
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_30,c_358])).

tff(c_375,plain,(
    ! [B_103] :
      ( k3_orders_2('#skF_2',B_103,'#skF_1'('#skF_2',B_103,'#skF_3')) = '#skF_3'
      | ~ m1_orders_2('#skF_3','#skF_2',B_103)
      | k1_xboole_0 = B_103
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_364])).

tff(c_466,plain,(
    ! [B_114] :
      ( k3_orders_2('#skF_2',B_114,'#skF_1'('#skF_2',B_114,'#skF_3')) = '#skF_3'
      | ~ m1_orders_2('#skF_3','#skF_2',B_114)
      | k1_xboole_0 = B_114
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_375])).

tff(c_470,plain,
    ( k3_orders_2('#skF_2','#skF_4','#skF_1'('#skF_2','#skF_4','#skF_3')) = '#skF_3'
    | ~ m1_orders_2('#skF_3','#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_28,c_466])).

tff(c_476,plain,
    ( k3_orders_2('#skF_2','#skF_4','#skF_1'('#skF_2','#skF_4','#skF_3')) = '#skF_3'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_470])).

tff(c_477,plain,(
    k3_orders_2('#skF_2','#skF_4','#skF_1'('#skF_2','#skF_4','#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_336,c_476])).

tff(c_488,plain,
    ( ~ r2_hidden('#skF_1'('#skF_2','#skF_4','#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_477,c_20])).

tff(c_501,plain,
    ( ~ r2_hidden('#skF_1'('#skF_2','#skF_4','#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_28,c_488])).

tff(c_502,plain,
    ( ~ r2_hidden('#skF_1'('#skF_2','#skF_4','#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_501])).

tff(c_504,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_502])).

tff(c_508,plain,
    ( ~ m1_orders_2('#skF_3','#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_504])).

tff(c_511,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_28,c_30,c_24,c_508])).

tff(c_513,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_336,c_511])).

tff(c_514,plain,(
    ~ r2_hidden('#skF_1'('#skF_2','#skF_4','#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_502])).

tff(c_335,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_4','#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_318])).

tff(c_515,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_502])).

tff(c_362,plain,(
    ! [B_103] :
      ( k3_orders_2('#skF_2',B_103,'#skF_1'('#skF_2',B_103,'#skF_4')) = '#skF_4'
      | ~ m1_orders_2('#skF_4','#skF_2',B_103)
      | k1_xboole_0 = B_103
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_358])).

tff(c_371,plain,(
    ! [B_103] :
      ( k3_orders_2('#skF_2',B_103,'#skF_1'('#skF_2',B_103,'#skF_4')) = '#skF_4'
      | ~ m1_orders_2('#skF_4','#skF_2',B_103)
      | k1_xboole_0 = B_103
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_362])).

tff(c_377,plain,(
    ! [B_105] :
      ( k3_orders_2('#skF_2',B_105,'#skF_1'('#skF_2',B_105,'#skF_4')) = '#skF_4'
      | ~ m1_orders_2('#skF_4','#skF_2',B_105)
      | k1_xboole_0 = B_105
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_371])).

tff(c_383,plain,
    ( k3_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3','#skF_4')) = '#skF_4'
    | ~ m1_orders_2('#skF_4','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_30,c_377])).

tff(c_389,plain,
    ( k3_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3','#skF_4')) = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_383])).

tff(c_390,plain,(
    k3_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3','#skF_4')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_389])).

tff(c_397,plain,
    ( ~ r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_390,c_20])).

tff(c_407,plain,
    ( ~ r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_30,c_397])).

tff(c_408,plain,
    ( ~ r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_407])).

tff(c_429,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_408])).

tff(c_432,plain,
    ( ~ m1_orders_2('#skF_4','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_429])).

tff(c_435,plain,
    ( k1_xboole_0 = '#skF_3'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_30,c_28,c_22,c_432])).

tff(c_437,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_26,c_435])).

tff(c_439,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_408])).

tff(c_395,plain,(
    ! [B_31] :
      ( r2_hidden(B_31,'#skF_3')
      | ~ r2_hidden(B_31,'#skF_4')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_31,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_390,c_16])).

tff(c_404,plain,(
    ! [B_31] :
      ( r2_hidden(B_31,'#skF_3')
      | ~ r2_hidden(B_31,'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_31,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_30,c_395])).

tff(c_405,plain,(
    ! [B_31] :
      ( r2_hidden(B_31,'#skF_3')
      | ~ r2_hidden(B_31,'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_31,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_404])).

tff(c_440,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_405])).

tff(c_442,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_439,c_440])).

tff(c_443,plain,(
    ! [B_31] :
      ( r2_hidden(B_31,'#skF_3')
      | ~ r2_hidden(B_31,'#skF_4')
      | ~ m1_subset_1(B_31,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_405])).

tff(c_518,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_4','#skF_3'),'#skF_3')
    | ~ r2_hidden('#skF_1'('#skF_2','#skF_4','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_515,c_443])).

tff(c_521,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_4','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_335,c_518])).

tff(c_523,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_514,c_521])).

tff(c_525,plain,(
    m1_orders_2('#skF_4','#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_301])).

tff(c_528,plain,(
    ! [B_118] :
      ( r2_hidden('#skF_1'('#skF_2',B_118,'#skF_3'),B_118)
      | ~ m1_orders_2('#skF_3','#skF_2',B_118)
      | k1_xboole_0 = B_118
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_291])).

tff(c_532,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_4','#skF_3'),'#skF_4')
    | ~ m1_orders_2('#skF_3','#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_28,c_528])).

tff(c_538,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_4','#skF_3'),'#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_532])).

tff(c_542,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_538])).

tff(c_45,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ m1_orders_2('#skF_4','#skF_2',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_43])).

tff(c_50,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ m1_orders_2('#skF_4','#skF_2',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_45])).

tff(c_51,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ m1_orders_2('#skF_4','#skF_2',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_50])).

tff(c_271,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ m1_orders_2('#skF_4','#skF_2',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_51])).

tff(c_272,plain,(
    ~ m1_orders_2('#skF_4','#skF_2',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_271])).

tff(c_548,plain,(
    ~ m1_orders_2('#skF_4','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_542,c_272])).

tff(c_557,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_525,c_548])).

tff(c_559,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_538])).

tff(c_524,plain,
    ( k1_xboole_0 = '#skF_4'
    | r2_hidden('#skF_1'('#skF_2','#skF_4','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_301])).

tff(c_526,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_4','#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_524])).

tff(c_561,plain,(
    ! [A_119,B_120,C_121] :
      ( k3_orders_2(A_119,B_120,'#skF_1'(A_119,B_120,C_121)) = C_121
      | ~ m1_orders_2(C_121,A_119,B_120)
      | k1_xboole_0 = B_120
      | ~ m1_subset_1(C_121,k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ l1_orders_2(A_119)
      | ~ v5_orders_2(A_119)
      | ~ v4_orders_2(A_119)
      | ~ v3_orders_2(A_119)
      | v2_struct_0(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_565,plain,(
    ! [B_120] :
      ( k3_orders_2('#skF_2',B_120,'#skF_1'('#skF_2',B_120,'#skF_4')) = '#skF_4'
      | ~ m1_orders_2('#skF_4','#skF_2',B_120)
      | k1_xboole_0 = B_120
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_561])).

tff(c_574,plain,(
    ! [B_120] :
      ( k3_orders_2('#skF_2',B_120,'#skF_1'('#skF_2',B_120,'#skF_4')) = '#skF_4'
      | ~ m1_orders_2('#skF_4','#skF_2',B_120)
      | k1_xboole_0 = B_120
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_565])).

tff(c_678,plain,(
    ! [B_129] :
      ( k3_orders_2('#skF_2',B_129,'#skF_1'('#skF_2',B_129,'#skF_4')) = '#skF_4'
      | ~ m1_orders_2('#skF_4','#skF_2',B_129)
      | k1_xboole_0 = B_129
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_574])).

tff(c_682,plain,
    ( k3_orders_2('#skF_2','#skF_4','#skF_1'('#skF_2','#skF_4','#skF_4')) = '#skF_4'
    | ~ m1_orders_2('#skF_4','#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_28,c_678])).

tff(c_688,plain,
    ( k3_orders_2('#skF_2','#skF_4','#skF_1'('#skF_2','#skF_4','#skF_4')) = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_525,c_682])).

tff(c_689,plain,(
    k3_orders_2('#skF_2','#skF_4','#skF_1'('#skF_2','#skF_4','#skF_4')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_559,c_688])).

tff(c_719,plain,
    ( ~ r2_hidden('#skF_1'('#skF_2','#skF_4','#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_4','#skF_4'),u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_689,c_20])).

tff(c_729,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_2','#skF_4','#skF_4'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_28,c_526,c_719])).

tff(c_730,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2','#skF_4','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_729])).

tff(c_734,plain,
    ( ~ m1_orders_2('#skF_4','#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_730])).

tff(c_737,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_28,c_525,c_734])).

tff(c_739,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_559,c_737])).

tff(c_740,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_524])).

tff(c_744,plain,(
    ~ m1_orders_2('#skF_4','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_740,c_272])).

tff(c_753,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_525,c_744])).

tff(c_754,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_271])).

tff(c_254,plain,(
    ~ m1_orders_2('#skF_3','#skF_2',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_55])).

tff(c_758,plain,(
    ~ m1_orders_2('#skF_3','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_754,c_254])).

tff(c_765,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_758])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:55:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.10/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.46  
% 3.15/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.47  %$ r2_orders_2 > m1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.15/1.47  
% 3.15/1.47  %Foreground sorts:
% 3.15/1.47  
% 3.15/1.47  
% 3.15/1.47  %Background operators:
% 3.15/1.47  
% 3.15/1.47  
% 3.15/1.47  %Foreground operators:
% 3.15/1.47  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.15/1.47  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.15/1.47  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.15/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.15/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.15/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.15/1.47  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 3.15/1.47  tff('#skF_2', type, '#skF_2': $i).
% 3.15/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.15/1.47  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.15/1.47  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.15/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.15/1.47  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.15/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.15/1.47  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 3.15/1.47  tff('#skF_4', type, '#skF_4': $i).
% 3.15/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.15/1.47  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 3.15/1.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.15/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.15/1.47  
% 3.15/1.49  tff(f_132, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~((~(B = k1_xboole_0) & m1_orders_2(B, A, C)) & m1_orders_2(C, A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_orders_2)).
% 3.15/1.49  tff(f_60, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((~(B = k1_xboole_0) => (m1_orders_2(C, A, B) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(A)) & r2_hidden(D, B)) & (C = k3_orders_2(A, B, D)))))) & ((B = k1_xboole_0) => (m1_orders_2(C, A, B) <=> (C = k1_xboole_0)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d15_orders_2)).
% 3.15/1.49  tff(f_106, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~r2_hidden(B, k3_orders_2(A, C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_orders_2)).
% 3.15/1.49  tff(f_86, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_orders_2)).
% 3.15/1.49  tff(c_24, plain, (m1_orders_2('#skF_3', '#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.15/1.49  tff(c_40, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.15/1.49  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.15/1.49  tff(c_38, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.15/1.49  tff(c_36, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.15/1.49  tff(c_34, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.15/1.49  tff(c_32, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.15/1.49  tff(c_274, plain, (![A_89, B_90, C_91]: (r2_hidden('#skF_1'(A_89, B_90, C_91), B_90) | ~m1_orders_2(C_91, A_89, B_90) | k1_xboole_0=B_90 | ~m1_subset_1(C_91, k1_zfmisc_1(u1_struct_0(A_89))) | ~m1_subset_1(B_90, k1_zfmisc_1(u1_struct_0(A_89))) | ~l1_orders_2(A_89) | ~v5_orders_2(A_89) | ~v4_orders_2(A_89) | ~v3_orders_2(A_89) | v2_struct_0(A_89))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.15/1.49  tff(c_278, plain, (![B_90]: (r2_hidden('#skF_1'('#skF_2', B_90, '#skF_4'), B_90) | ~m1_orders_2('#skF_4', '#skF_2', B_90) | k1_xboole_0=B_90 | ~m1_subset_1(B_90, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_274])).
% 3.15/1.49  tff(c_287, plain, (![B_90]: (r2_hidden('#skF_1'('#skF_2', B_90, '#skF_4'), B_90) | ~m1_orders_2('#skF_4', '#skF_2', B_90) | k1_xboole_0=B_90 | ~m1_subset_1(B_90, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_278])).
% 3.15/1.49  tff(c_293, plain, (![B_92]: (r2_hidden('#skF_1'('#skF_2', B_92, '#skF_4'), B_92) | ~m1_orders_2('#skF_4', '#skF_2', B_92) | k1_xboole_0=B_92 | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_40, c_287])).
% 3.15/1.49  tff(c_301, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_4', '#skF_4'), '#skF_4') | ~m1_orders_2('#skF_4', '#skF_2', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_28, c_293])).
% 3.15/1.49  tff(c_307, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_301])).
% 3.15/1.49  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.15/1.49  tff(c_280, plain, (![B_90]: (r2_hidden('#skF_1'('#skF_2', B_90, '#skF_3'), B_90) | ~m1_orders_2('#skF_3', '#skF_2', B_90) | k1_xboole_0=B_90 | ~m1_subset_1(B_90, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_274])).
% 3.15/1.49  tff(c_291, plain, (![B_90]: (r2_hidden('#skF_1'('#skF_2', B_90, '#skF_3'), B_90) | ~m1_orders_2('#skF_3', '#skF_2', B_90) | k1_xboole_0=B_90 | ~m1_subset_1(B_90, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_280])).
% 3.15/1.49  tff(c_308, plain, (![B_97]: (r2_hidden('#skF_1'('#skF_2', B_97, '#skF_3'), B_97) | ~m1_orders_2('#skF_3', '#skF_2', B_97) | k1_xboole_0=B_97 | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_40, c_291])).
% 3.15/1.49  tff(c_312, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_4', '#skF_3'), '#skF_4') | ~m1_orders_2('#skF_3', '#skF_2', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_28, c_308])).
% 3.15/1.49  tff(c_318, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_4', '#skF_3'), '#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_312])).
% 3.15/1.49  tff(c_322, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_318])).
% 3.15/1.49  tff(c_57, plain, (![A_55, B_56, C_57]: (r2_hidden('#skF_1'(A_55, B_56, C_57), B_56) | ~m1_orders_2(C_57, A_55, B_56) | k1_xboole_0=B_56 | ~m1_subset_1(C_57, k1_zfmisc_1(u1_struct_0(A_55))) | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0(A_55))) | ~l1_orders_2(A_55) | ~v5_orders_2(A_55) | ~v4_orders_2(A_55) | ~v3_orders_2(A_55) | v2_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.15/1.49  tff(c_61, plain, (![B_56]: (r2_hidden('#skF_1'('#skF_2', B_56, '#skF_3'), B_56) | ~m1_orders_2('#skF_3', '#skF_2', B_56) | k1_xboole_0=B_56 | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_57])).
% 3.15/1.49  tff(c_68, plain, (![B_56]: (r2_hidden('#skF_1'('#skF_2', B_56, '#skF_3'), B_56) | ~m1_orders_2('#skF_3', '#skF_2', B_56) | k1_xboole_0=B_56 | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_61])).
% 3.15/1.49  tff(c_81, plain, (![B_59]: (r2_hidden('#skF_1'('#skF_2', B_59, '#skF_3'), B_59) | ~m1_orders_2('#skF_3', '#skF_2', B_59) | k1_xboole_0=B_59 | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_40, c_68])).
% 3.15/1.49  tff(c_83, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_4', '#skF_3'), '#skF_4') | ~m1_orders_2('#skF_3', '#skF_2', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_28, c_81])).
% 3.15/1.49  tff(c_88, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_4', '#skF_3'), '#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_83])).
% 3.15/1.49  tff(c_92, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_88])).
% 3.15/1.49  tff(c_26, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.15/1.49  tff(c_43, plain, (![C_53, A_54]: (k1_xboole_0=C_53 | ~m1_orders_2(C_53, A_54, k1_xboole_0) | ~m1_subset_1(C_53, k1_zfmisc_1(u1_struct_0(A_54))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_54))) | ~l1_orders_2(A_54) | ~v5_orders_2(A_54) | ~v4_orders_2(A_54) | ~v3_orders_2(A_54) | v2_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.15/1.49  tff(c_47, plain, (k1_xboole_0='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_30, c_43])).
% 3.15/1.49  tff(c_54, plain, (k1_xboole_0='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_47])).
% 3.15/1.49  tff(c_55, plain, (~m1_orders_2('#skF_3', '#skF_2', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_40, c_26, c_54])).
% 3.15/1.49  tff(c_56, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_55])).
% 3.15/1.49  tff(c_96, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_56])).
% 3.15/1.49  tff(c_102, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_96])).
% 3.15/1.49  tff(c_104, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_88])).
% 3.15/1.49  tff(c_12, plain, (![A_1, B_13, C_19]: (m1_subset_1('#skF_1'(A_1, B_13, C_19), u1_struct_0(A_1)) | ~m1_orders_2(C_19, A_1, B_13) | k1_xboole_0=B_13 | ~m1_subset_1(C_19, k1_zfmisc_1(u1_struct_0(A_1))) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_orders_2(A_1) | ~v5_orders_2(A_1) | ~v4_orders_2(A_1) | ~v3_orders_2(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.15/1.49  tff(c_109, plain, (![A_71, B_72, C_73]: (k3_orders_2(A_71, B_72, '#skF_1'(A_71, B_72, C_73))=C_73 | ~m1_orders_2(C_73, A_71, B_72) | k1_xboole_0=B_72 | ~m1_subset_1(C_73, k1_zfmisc_1(u1_struct_0(A_71))) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_orders_2(A_71) | ~v5_orders_2(A_71) | ~v4_orders_2(A_71) | ~v3_orders_2(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.15/1.49  tff(c_113, plain, (![B_72]: (k3_orders_2('#skF_2', B_72, '#skF_1'('#skF_2', B_72, '#skF_3'))='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', B_72) | k1_xboole_0=B_72 | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_109])).
% 3.15/1.49  tff(c_120, plain, (![B_72]: (k3_orders_2('#skF_2', B_72, '#skF_1'('#skF_2', B_72, '#skF_3'))='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', B_72) | k1_xboole_0=B_72 | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_113])).
% 3.15/1.49  tff(c_192, plain, (![B_80]: (k3_orders_2('#skF_2', B_80, '#skF_1'('#skF_2', B_80, '#skF_3'))='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', B_80) | k1_xboole_0=B_80 | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_40, c_120])).
% 3.15/1.49  tff(c_194, plain, (k3_orders_2('#skF_2', '#skF_4', '#skF_1'('#skF_2', '#skF_4', '#skF_3'))='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_28, c_192])).
% 3.15/1.49  tff(c_199, plain, (k3_orders_2('#skF_2', '#skF_4', '#skF_1'('#skF_2', '#skF_4', '#skF_3'))='#skF_3' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_194])).
% 3.15/1.49  tff(c_200, plain, (k3_orders_2('#skF_2', '#skF_4', '#skF_1'('#skF_2', '#skF_4', '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_104, c_199])).
% 3.15/1.49  tff(c_20, plain, (![B_42, A_38, C_44]: (~r2_hidden(B_42, k3_orders_2(A_38, C_44, B_42)) | ~m1_subset_1(C_44, k1_zfmisc_1(u1_struct_0(A_38))) | ~m1_subset_1(B_42, u1_struct_0(A_38)) | ~l1_orders_2(A_38) | ~v5_orders_2(A_38) | ~v4_orders_2(A_38) | ~v3_orders_2(A_38) | v2_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.15/1.49  tff(c_209, plain, (~r2_hidden('#skF_1'('#skF_2', '#skF_4', '#skF_3'), '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_200, c_20])).
% 3.15/1.49  tff(c_219, plain, (~r2_hidden('#skF_1'('#skF_2', '#skF_4', '#skF_3'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_28, c_209])).
% 3.15/1.49  tff(c_220, plain, (~r2_hidden('#skF_1'('#skF_2', '#skF_4', '#skF_3'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_40, c_219])).
% 3.15/1.49  tff(c_222, plain, (~m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_220])).
% 3.15/1.49  tff(c_225, plain, (~m1_orders_2('#skF_3', '#skF_2', '#skF_4') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_12, c_222])).
% 3.15/1.49  tff(c_228, plain, (k1_xboole_0='#skF_4' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_28, c_30, c_24, c_225])).
% 3.15/1.49  tff(c_230, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_104, c_228])).
% 3.15/1.49  tff(c_231, plain, (~r2_hidden('#skF_1'('#skF_2', '#skF_4', '#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_220])).
% 3.15/1.49  tff(c_103, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_4', '#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_88])).
% 3.15/1.49  tff(c_232, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_220])).
% 3.15/1.49  tff(c_22, plain, (m1_orders_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.15/1.49  tff(c_111, plain, (![B_72]: (k3_orders_2('#skF_2', B_72, '#skF_1'('#skF_2', B_72, '#skF_4'))='#skF_4' | ~m1_orders_2('#skF_4', '#skF_2', B_72) | k1_xboole_0=B_72 | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_109])).
% 3.15/1.49  tff(c_116, plain, (![B_72]: (k3_orders_2('#skF_2', B_72, '#skF_1'('#skF_2', B_72, '#skF_4'))='#skF_4' | ~m1_orders_2('#skF_4', '#skF_2', B_72) | k1_xboole_0=B_72 | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_111])).
% 3.15/1.49  tff(c_122, plain, (![B_74]: (k3_orders_2('#skF_2', B_74, '#skF_1'('#skF_2', B_74, '#skF_4'))='#skF_4' | ~m1_orders_2('#skF_4', '#skF_2', B_74) | k1_xboole_0=B_74 | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_40, c_116])).
% 3.15/1.49  tff(c_126, plain, (k3_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_4'))='#skF_4' | ~m1_orders_2('#skF_4', '#skF_2', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_30, c_122])).
% 3.15/1.49  tff(c_131, plain, (k3_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_4'))='#skF_4' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_126])).
% 3.15/1.49  tff(c_132, plain, (k3_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_4'))='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_26, c_131])).
% 3.15/1.49  tff(c_139, plain, (~r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_132, c_20])).
% 3.15/1.49  tff(c_149, plain, (~r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_4') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_30, c_139])).
% 3.15/1.49  tff(c_150, plain, (~r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_4') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_40, c_149])).
% 3.15/1.49  tff(c_152, plain, (~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_150])).
% 3.15/1.49  tff(c_168, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_3') | k1_xboole_0='#skF_3' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_12, c_152])).
% 3.15/1.49  tff(c_171, plain, (k1_xboole_0='#skF_3' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_30, c_28, c_22, c_168])).
% 3.15/1.49  tff(c_173, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_26, c_171])).
% 3.15/1.49  tff(c_175, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_150])).
% 3.15/1.49  tff(c_16, plain, (![B_31, D_37, A_23, C_35]: (r2_hidden(B_31, D_37) | ~r2_hidden(B_31, k3_orders_2(A_23, D_37, C_35)) | ~m1_subset_1(D_37, k1_zfmisc_1(u1_struct_0(A_23))) | ~m1_subset_1(C_35, u1_struct_0(A_23)) | ~m1_subset_1(B_31, u1_struct_0(A_23)) | ~l1_orders_2(A_23) | ~v5_orders_2(A_23) | ~v4_orders_2(A_23) | ~v3_orders_2(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.15/1.49  tff(c_137, plain, (![B_31]: (r2_hidden(B_31, '#skF_3') | ~r2_hidden(B_31, '#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_31, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_132, c_16])).
% 3.15/1.49  tff(c_146, plain, (![B_31]: (r2_hidden(B_31, '#skF_3') | ~r2_hidden(B_31, '#skF_4') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_31, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_30, c_137])).
% 3.15/1.49  tff(c_147, plain, (![B_31]: (r2_hidden(B_31, '#skF_3') | ~r2_hidden(B_31, '#skF_4') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_31, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_40, c_146])).
% 3.15/1.49  tff(c_177, plain, (![B_31]: (r2_hidden(B_31, '#skF_3') | ~r2_hidden(B_31, '#skF_4') | ~m1_subset_1(B_31, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_175, c_147])).
% 3.15/1.49  tff(c_248, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_4', '#skF_3'), '#skF_3') | ~r2_hidden('#skF_1'('#skF_2', '#skF_4', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_232, c_177])).
% 3.15/1.49  tff(c_251, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_4', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_248])).
% 3.15/1.49  tff(c_253, plain, $false, inference(negUnitSimplification, [status(thm)], [c_231, c_251])).
% 3.15/1.49  tff(c_255, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_55])).
% 3.15/1.49  tff(c_2, plain, (![A_1]: (m1_orders_2(k1_xboole_0, A_1, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_orders_2(A_1) | ~v5_orders_2(A_1) | ~v4_orders_2(A_1) | ~v3_orders_2(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.15/1.49  tff(c_260, plain, (m1_orders_2(k1_xboole_0, '#skF_2', k1_xboole_0) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_255, c_2])).
% 3.15/1.49  tff(c_268, plain, (m1_orders_2(k1_xboole_0, '#skF_2', k1_xboole_0) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_260])).
% 3.15/1.49  tff(c_269, plain, (m1_orders_2(k1_xboole_0, '#skF_2', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_40, c_268])).
% 3.15/1.49  tff(c_327, plain, (m1_orders_2('#skF_4', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_322, c_322, c_269])).
% 3.15/1.49  tff(c_334, plain, $false, inference(negUnitSimplification, [status(thm)], [c_307, c_327])).
% 3.15/1.49  tff(c_336, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_318])).
% 3.15/1.49  tff(c_358, plain, (![A_102, B_103, C_104]: (k3_orders_2(A_102, B_103, '#skF_1'(A_102, B_103, C_104))=C_104 | ~m1_orders_2(C_104, A_102, B_103) | k1_xboole_0=B_103 | ~m1_subset_1(C_104, k1_zfmisc_1(u1_struct_0(A_102))) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_orders_2(A_102) | ~v5_orders_2(A_102) | ~v4_orders_2(A_102) | ~v3_orders_2(A_102) | v2_struct_0(A_102))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.15/1.49  tff(c_364, plain, (![B_103]: (k3_orders_2('#skF_2', B_103, '#skF_1'('#skF_2', B_103, '#skF_3'))='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', B_103) | k1_xboole_0=B_103 | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_358])).
% 3.15/1.49  tff(c_375, plain, (![B_103]: (k3_orders_2('#skF_2', B_103, '#skF_1'('#skF_2', B_103, '#skF_3'))='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', B_103) | k1_xboole_0=B_103 | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_364])).
% 3.15/1.49  tff(c_466, plain, (![B_114]: (k3_orders_2('#skF_2', B_114, '#skF_1'('#skF_2', B_114, '#skF_3'))='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', B_114) | k1_xboole_0=B_114 | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_40, c_375])).
% 3.15/1.49  tff(c_470, plain, (k3_orders_2('#skF_2', '#skF_4', '#skF_1'('#skF_2', '#skF_4', '#skF_3'))='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_28, c_466])).
% 3.15/1.49  tff(c_476, plain, (k3_orders_2('#skF_2', '#skF_4', '#skF_1'('#skF_2', '#skF_4', '#skF_3'))='#skF_3' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_470])).
% 3.15/1.49  tff(c_477, plain, (k3_orders_2('#skF_2', '#skF_4', '#skF_1'('#skF_2', '#skF_4', '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_336, c_476])).
% 3.15/1.49  tff(c_488, plain, (~r2_hidden('#skF_1'('#skF_2', '#skF_4', '#skF_3'), '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_477, c_20])).
% 3.15/1.49  tff(c_501, plain, (~r2_hidden('#skF_1'('#skF_2', '#skF_4', '#skF_3'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_28, c_488])).
% 3.15/1.49  tff(c_502, plain, (~r2_hidden('#skF_1'('#skF_2', '#skF_4', '#skF_3'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_40, c_501])).
% 3.15/1.49  tff(c_504, plain, (~m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_502])).
% 3.15/1.49  tff(c_508, plain, (~m1_orders_2('#skF_3', '#skF_2', '#skF_4') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_12, c_504])).
% 3.15/1.49  tff(c_511, plain, (k1_xboole_0='#skF_4' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_28, c_30, c_24, c_508])).
% 3.15/1.49  tff(c_513, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_336, c_511])).
% 3.15/1.49  tff(c_514, plain, (~r2_hidden('#skF_1'('#skF_2', '#skF_4', '#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_502])).
% 3.15/1.49  tff(c_335, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_4', '#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_318])).
% 3.15/1.49  tff(c_515, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_502])).
% 3.15/1.49  tff(c_362, plain, (![B_103]: (k3_orders_2('#skF_2', B_103, '#skF_1'('#skF_2', B_103, '#skF_4'))='#skF_4' | ~m1_orders_2('#skF_4', '#skF_2', B_103) | k1_xboole_0=B_103 | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_358])).
% 3.15/1.49  tff(c_371, plain, (![B_103]: (k3_orders_2('#skF_2', B_103, '#skF_1'('#skF_2', B_103, '#skF_4'))='#skF_4' | ~m1_orders_2('#skF_4', '#skF_2', B_103) | k1_xboole_0=B_103 | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_362])).
% 3.15/1.49  tff(c_377, plain, (![B_105]: (k3_orders_2('#skF_2', B_105, '#skF_1'('#skF_2', B_105, '#skF_4'))='#skF_4' | ~m1_orders_2('#skF_4', '#skF_2', B_105) | k1_xboole_0=B_105 | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_40, c_371])).
% 3.15/1.49  tff(c_383, plain, (k3_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_4'))='#skF_4' | ~m1_orders_2('#skF_4', '#skF_2', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_30, c_377])).
% 3.15/1.49  tff(c_389, plain, (k3_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_4'))='#skF_4' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_383])).
% 3.15/1.49  tff(c_390, plain, (k3_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_4'))='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_26, c_389])).
% 3.15/1.49  tff(c_397, plain, (~r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_390, c_20])).
% 3.15/1.49  tff(c_407, plain, (~r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_4') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_30, c_397])).
% 3.15/1.49  tff(c_408, plain, (~r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_4') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_40, c_407])).
% 3.15/1.49  tff(c_429, plain, (~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_408])).
% 3.15/1.49  tff(c_432, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_3') | k1_xboole_0='#skF_3' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_12, c_429])).
% 3.15/1.49  tff(c_435, plain, (k1_xboole_0='#skF_3' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_30, c_28, c_22, c_432])).
% 3.15/1.49  tff(c_437, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_26, c_435])).
% 3.15/1.49  tff(c_439, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_408])).
% 3.15/1.49  tff(c_395, plain, (![B_31]: (r2_hidden(B_31, '#skF_3') | ~r2_hidden(B_31, '#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_31, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_390, c_16])).
% 3.15/1.49  tff(c_404, plain, (![B_31]: (r2_hidden(B_31, '#skF_3') | ~r2_hidden(B_31, '#skF_4') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_31, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_30, c_395])).
% 3.15/1.49  tff(c_405, plain, (![B_31]: (r2_hidden(B_31, '#skF_3') | ~r2_hidden(B_31, '#skF_4') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_31, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_40, c_404])).
% 3.15/1.49  tff(c_440, plain, (~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_405])).
% 3.15/1.49  tff(c_442, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_439, c_440])).
% 3.15/1.49  tff(c_443, plain, (![B_31]: (r2_hidden(B_31, '#skF_3') | ~r2_hidden(B_31, '#skF_4') | ~m1_subset_1(B_31, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_405])).
% 3.15/1.49  tff(c_518, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_4', '#skF_3'), '#skF_3') | ~r2_hidden('#skF_1'('#skF_2', '#skF_4', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_515, c_443])).
% 3.15/1.49  tff(c_521, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_4', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_335, c_518])).
% 3.15/1.49  tff(c_523, plain, $false, inference(negUnitSimplification, [status(thm)], [c_514, c_521])).
% 3.15/1.49  tff(c_525, plain, (m1_orders_2('#skF_4', '#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_301])).
% 3.15/1.49  tff(c_528, plain, (![B_118]: (r2_hidden('#skF_1'('#skF_2', B_118, '#skF_3'), B_118) | ~m1_orders_2('#skF_3', '#skF_2', B_118) | k1_xboole_0=B_118 | ~m1_subset_1(B_118, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_40, c_291])).
% 3.15/1.49  tff(c_532, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_4', '#skF_3'), '#skF_4') | ~m1_orders_2('#skF_3', '#skF_2', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_28, c_528])).
% 3.15/1.49  tff(c_538, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_4', '#skF_3'), '#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_532])).
% 3.15/1.49  tff(c_542, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_538])).
% 3.15/1.49  tff(c_45, plain, (k1_xboole_0='#skF_4' | ~m1_orders_2('#skF_4', '#skF_2', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_28, c_43])).
% 3.15/1.49  tff(c_50, plain, (k1_xboole_0='#skF_4' | ~m1_orders_2('#skF_4', '#skF_2', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_45])).
% 3.15/1.49  tff(c_51, plain, (k1_xboole_0='#skF_4' | ~m1_orders_2('#skF_4', '#skF_2', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_40, c_50])).
% 3.15/1.49  tff(c_271, plain, (k1_xboole_0='#skF_4' | ~m1_orders_2('#skF_4', '#skF_2', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_255, c_51])).
% 3.15/1.49  tff(c_272, plain, (~m1_orders_2('#skF_4', '#skF_2', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_271])).
% 3.15/1.49  tff(c_548, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_542, c_272])).
% 3.15/1.49  tff(c_557, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_525, c_548])).
% 3.15/1.49  tff(c_559, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_538])).
% 3.15/1.49  tff(c_524, plain, (k1_xboole_0='#skF_4' | r2_hidden('#skF_1'('#skF_2', '#skF_4', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_301])).
% 3.15/1.49  tff(c_526, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_4', '#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_524])).
% 3.15/1.49  tff(c_561, plain, (![A_119, B_120, C_121]: (k3_orders_2(A_119, B_120, '#skF_1'(A_119, B_120, C_121))=C_121 | ~m1_orders_2(C_121, A_119, B_120) | k1_xboole_0=B_120 | ~m1_subset_1(C_121, k1_zfmisc_1(u1_struct_0(A_119))) | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0(A_119))) | ~l1_orders_2(A_119) | ~v5_orders_2(A_119) | ~v4_orders_2(A_119) | ~v3_orders_2(A_119) | v2_struct_0(A_119))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.15/1.49  tff(c_565, plain, (![B_120]: (k3_orders_2('#skF_2', B_120, '#skF_1'('#skF_2', B_120, '#skF_4'))='#skF_4' | ~m1_orders_2('#skF_4', '#skF_2', B_120) | k1_xboole_0=B_120 | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_561])).
% 3.15/1.49  tff(c_574, plain, (![B_120]: (k3_orders_2('#skF_2', B_120, '#skF_1'('#skF_2', B_120, '#skF_4'))='#skF_4' | ~m1_orders_2('#skF_4', '#skF_2', B_120) | k1_xboole_0=B_120 | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_565])).
% 3.15/1.49  tff(c_678, plain, (![B_129]: (k3_orders_2('#skF_2', B_129, '#skF_1'('#skF_2', B_129, '#skF_4'))='#skF_4' | ~m1_orders_2('#skF_4', '#skF_2', B_129) | k1_xboole_0=B_129 | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_40, c_574])).
% 3.15/1.49  tff(c_682, plain, (k3_orders_2('#skF_2', '#skF_4', '#skF_1'('#skF_2', '#skF_4', '#skF_4'))='#skF_4' | ~m1_orders_2('#skF_4', '#skF_2', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_28, c_678])).
% 3.15/1.49  tff(c_688, plain, (k3_orders_2('#skF_2', '#skF_4', '#skF_1'('#skF_2', '#skF_4', '#skF_4'))='#skF_4' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_525, c_682])).
% 3.15/1.49  tff(c_689, plain, (k3_orders_2('#skF_2', '#skF_4', '#skF_1'('#skF_2', '#skF_4', '#skF_4'))='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_559, c_688])).
% 3.15/1.49  tff(c_719, plain, (~r2_hidden('#skF_1'('#skF_2', '#skF_4', '#skF_4'), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_4'), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_689, c_20])).
% 3.15/1.49  tff(c_729, plain, (~m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_4'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_28, c_526, c_719])).
% 3.15/1.49  tff(c_730, plain, (~m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_4'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_40, c_729])).
% 3.15/1.49  tff(c_734, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_4') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_12, c_730])).
% 3.15/1.49  tff(c_737, plain, (k1_xboole_0='#skF_4' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_28, c_525, c_734])).
% 3.15/1.49  tff(c_739, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_559, c_737])).
% 3.15/1.49  tff(c_740, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_524])).
% 3.15/1.49  tff(c_744, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_740, c_272])).
% 3.15/1.49  tff(c_753, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_525, c_744])).
% 3.15/1.49  tff(c_754, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_271])).
% 3.15/1.49  tff(c_254, plain, (~m1_orders_2('#skF_3', '#skF_2', k1_xboole_0)), inference(splitRight, [status(thm)], [c_55])).
% 3.15/1.49  tff(c_758, plain, (~m1_orders_2('#skF_3', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_754, c_254])).
% 3.15/1.49  tff(c_765, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_758])).
% 3.15/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.49  
% 3.15/1.49  Inference rules
% 3.15/1.49  ----------------------
% 3.15/1.49  #Ref     : 0
% 3.15/1.50  #Sup     : 113
% 3.15/1.50  #Fact    : 0
% 3.15/1.50  #Define  : 0
% 3.15/1.50  #Split   : 23
% 3.15/1.50  #Chain   : 0
% 3.15/1.50  #Close   : 0
% 3.15/1.50  
% 3.15/1.50  Ordering : KBO
% 3.15/1.50  
% 3.15/1.50  Simplification rules
% 3.15/1.50  ----------------------
% 3.15/1.50  #Subsume      : 17
% 3.15/1.50  #Demod        : 383
% 3.15/1.50  #Tautology    : 22
% 3.15/1.50  #SimpNegUnit  : 83
% 3.15/1.50  #BackRed      : 43
% 3.15/1.50  
% 3.15/1.50  #Partial instantiations: 0
% 3.15/1.50  #Strategies tried      : 1
% 3.15/1.50  
% 3.15/1.50  Timing (in seconds)
% 3.15/1.50  ----------------------
% 3.15/1.50  Preprocessing        : 0.32
% 3.15/1.50  Parsing              : 0.16
% 3.15/1.50  CNF conversion       : 0.03
% 3.15/1.50  Main loop            : 0.37
% 3.15/1.50  Inferencing          : 0.12
% 3.15/1.50  Reduction            : 0.13
% 3.15/1.50  Demodulation         : 0.09
% 3.15/1.50  BG Simplification    : 0.02
% 3.15/1.50  Subsumption          : 0.07
% 3.15/1.50  Abstraction          : 0.02
% 3.15/1.50  MUC search           : 0.00
% 3.15/1.50  Cooper               : 0.00
% 3.15/1.50  Total                : 0.75
% 3.15/1.50  Index Insertion      : 0.00
% 3.15/1.50  Index Deletion       : 0.00
% 3.15/1.50  Index Matching       : 0.00
% 3.15/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
