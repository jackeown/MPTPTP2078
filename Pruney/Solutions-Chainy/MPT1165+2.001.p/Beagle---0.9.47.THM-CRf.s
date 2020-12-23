%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:49 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 254 expanded)
%              Number of leaves         :   24 ( 106 expanded)
%              Depth                    :   14
%              Number of atoms          :  209 (1278 expanded)
%              Number of equality atoms :   33 ( 250 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r1_orders_2 > m1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

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

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_128,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ~ ( B != k1_xboole_0
                  & m1_orders_2(B,A,B) )
              & ~ ( ~ m1_orders_2(B,A,B)
                  & B = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_orders_2)).

tff(f_75,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_orders_2)).

tff(f_101,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).

tff(f_40,axiom,(
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

tff(c_36,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_44,plain,
    ( k1_xboole_0 != '#skF_3'
    | ~ m1_orders_2('#skF_3','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_45,plain,(
    ~ m1_orders_2('#skF_3','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_34,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_32,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_30,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_28,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_38,plain,
    ( m1_orders_2('#skF_3','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_46,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_38])).

tff(c_8,plain,(
    ! [A_8] :
      ( m1_orders_2(k1_xboole_0,A_8,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_orders_2(A_8)
      | ~ v5_orders_2(A_8)
      | ~ v4_orders_2(A_8)
      | ~ v3_orders_2(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_54,plain,(
    ! [A_51] :
      ( m1_orders_2('#skF_3',A_51,'#skF_3')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_orders_2(A_51)
      | ~ v5_orders_2(A_51)
      | ~ v4_orders_2(A_51)
      | ~ v3_orders_2(A_51)
      | v2_struct_0(A_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_46,c_46,c_8])).

tff(c_57,plain,
    ( m1_orders_2('#skF_3','#skF_2','#skF_3')
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_54])).

tff(c_60,plain,
    ( m1_orders_2('#skF_3','#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_28,c_57])).

tff(c_62,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_45,c_60])).

tff(c_63,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_64,plain,(
    m1_orders_2('#skF_3','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_18,plain,(
    ! [A_8,B_20,C_26] :
      ( m1_subset_1('#skF_1'(A_8,B_20,C_26),u1_struct_0(A_8))
      | ~ m1_orders_2(C_26,A_8,B_20)
      | k1_xboole_0 = B_20
      | ~ m1_subset_1(C_26,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_orders_2(A_8)
      | ~ v5_orders_2(A_8)
      | ~ v4_orders_2(A_8)
      | ~ v3_orders_2(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_99,plain,(
    ! [A_78,B_79,C_80] :
      ( k3_orders_2(A_78,B_79,'#skF_1'(A_78,B_79,C_80)) = C_80
      | ~ m1_orders_2(C_80,A_78,B_79)
      | k1_xboole_0 = B_79
      | ~ m1_subset_1(C_80,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_orders_2(A_78)
      | ~ v5_orders_2(A_78)
      | ~ v4_orders_2(A_78)
      | ~ v3_orders_2(A_78)
      | v2_struct_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_101,plain,(
    ! [B_79] :
      ( k3_orders_2('#skF_2',B_79,'#skF_1'('#skF_2',B_79,'#skF_3')) = '#skF_3'
      | ~ m1_orders_2('#skF_3','#skF_2',B_79)
      | k1_xboole_0 = B_79
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_99])).

tff(c_104,plain,(
    ! [B_79] :
      ( k3_orders_2('#skF_2',B_79,'#skF_1'('#skF_2',B_79,'#skF_3')) = '#skF_3'
      | ~ m1_orders_2('#skF_3','#skF_2',B_79)
      | k1_xboole_0 = B_79
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_28,c_101])).

tff(c_106,plain,(
    ! [B_81] :
      ( k3_orders_2('#skF_2',B_81,'#skF_1'('#skF_2',B_81,'#skF_3')) = '#skF_3'
      | ~ m1_orders_2('#skF_3','#skF_2',B_81)
      | k1_xboole_0 = B_81
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_104])).

tff(c_108,plain,
    ( k3_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3','#skF_3')) = '#skF_3'
    | ~ m1_orders_2('#skF_3','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_26,c_106])).

tff(c_111,plain,
    ( k3_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3','#skF_3')) = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_108])).

tff(c_112,plain,(
    k3_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3','#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_111])).

tff(c_24,plain,(
    ! [A_30,B_38,C_42,D_44] :
      ( r2_orders_2(A_30,B_38,C_42)
      | ~ r2_hidden(B_38,k3_orders_2(A_30,D_44,C_42))
      | ~ m1_subset_1(D_44,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ m1_subset_1(C_42,u1_struct_0(A_30))
      | ~ m1_subset_1(B_38,u1_struct_0(A_30))
      | ~ l1_orders_2(A_30)
      | ~ v5_orders_2(A_30)
      | ~ v4_orders_2(A_30)
      | ~ v3_orders_2(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_115,plain,(
    ! [B_38] :
      ( r2_orders_2('#skF_2',B_38,'#skF_1'('#skF_2','#skF_3','#skF_3'))
      | ~ r2_hidden(B_38,'#skF_3')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_3'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_24])).

tff(c_121,plain,(
    ! [B_38] :
      ( r2_orders_2('#skF_2',B_38,'#skF_1'('#skF_2','#skF_3','#skF_3'))
      | ~ r2_hidden(B_38,'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_3'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_28,c_26,c_115])).

tff(c_122,plain,(
    ! [B_38] :
      ( r2_orders_2('#skF_2',B_38,'#skF_1'('#skF_2','#skF_3','#skF_3'))
      | ~ r2_hidden(B_38,'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_3'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_121])).

tff(c_127,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_130,plain,
    ( ~ m1_orders_2('#skF_3','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_127])).

tff(c_133,plain,
    ( k1_xboole_0 = '#skF_3'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_28,c_26,c_64,c_130])).

tff(c_135,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_63,c_133])).

tff(c_137,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_79,plain,(
    ! [A_63,B_64,C_65] :
      ( r2_hidden('#skF_1'(A_63,B_64,C_65),B_64)
      | ~ m1_orders_2(C_65,A_63,B_64)
      | k1_xboole_0 = B_64
      | ~ m1_subset_1(C_65,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_orders_2(A_63)
      | ~ v5_orders_2(A_63)
      | ~ v4_orders_2(A_63)
      | ~ v3_orders_2(A_63)
      | v2_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_81,plain,(
    ! [B_64] :
      ( r2_hidden('#skF_1'('#skF_2',B_64,'#skF_3'),B_64)
      | ~ m1_orders_2('#skF_3','#skF_2',B_64)
      | k1_xboole_0 = B_64
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_79])).

tff(c_84,plain,(
    ! [B_64] :
      ( r2_hidden('#skF_1'('#skF_2',B_64,'#skF_3'),B_64)
      | ~ m1_orders_2('#skF_3','#skF_2',B_64)
      | k1_xboole_0 = B_64
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_28,c_81])).

tff(c_86,plain,(
    ! [B_66] :
      ( r2_hidden('#skF_1'('#skF_2',B_66,'#skF_3'),B_66)
      | ~ m1_orders_2('#skF_3','#skF_2',B_66)
      | k1_xboole_0 = B_66
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_84])).

tff(c_88,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_3'),'#skF_3')
    | ~ m1_orders_2('#skF_3','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_26,c_86])).

tff(c_91,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_3'),'#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_88])).

tff(c_92,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_91])).

tff(c_143,plain,(
    ! [B_82] :
      ( r2_orders_2('#skF_2',B_82,'#skF_1'('#skF_2','#skF_3','#skF_3'))
      | ~ r2_hidden(B_82,'#skF_3')
      | ~ m1_subset_1(B_82,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_4,plain,(
    ! [A_1,C_7] :
      ( ~ r2_orders_2(A_1,C_7,C_7)
      | ~ m1_subset_1(C_7,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_148,plain,
    ( ~ l1_orders_2('#skF_2')
    | ~ r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_143,c_4])).

tff(c_155,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_92,c_28,c_148])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:30:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.26/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.33  
% 2.26/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.33  %$ r2_orders_2 > r1_orders_2 > m1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.26/1.33  
% 2.26/1.33  %Foreground sorts:
% 2.26/1.33  
% 2.26/1.33  
% 2.26/1.33  %Background operators:
% 2.26/1.33  
% 2.26/1.33  
% 2.26/1.33  %Foreground operators:
% 2.26/1.33  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.26/1.33  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.26/1.33  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.26/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.26/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.26/1.33  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.26/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.26/1.33  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 2.26/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.26/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.26/1.33  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.26/1.33  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.26/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.26/1.33  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.26/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.26/1.33  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 2.26/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.26/1.33  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 2.26/1.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.26/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.26/1.33  
% 2.26/1.35  tff(f_128, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (~(~(B = k1_xboole_0) & m1_orders_2(B, A, B)) & ~(~m1_orders_2(B, A, B) & (B = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_orders_2)).
% 2.26/1.35  tff(f_75, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((~(B = k1_xboole_0) => (m1_orders_2(C, A, B) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(A)) & r2_hidden(D, B)) & (C = k3_orders_2(A, B, D)))))) & ((B = k1_xboole_0) => (m1_orders_2(C, A, B) <=> (C = k1_xboole_0)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d15_orders_2)).
% 2.26/1.35  tff(f_101, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_orders_2)).
% 2.26/1.35  tff(f_40, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_orders_2)).
% 2.26/1.35  tff(c_36, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.26/1.35  tff(c_44, plain, (k1_xboole_0!='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.26/1.35  tff(c_45, plain, (~m1_orders_2('#skF_3', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_44])).
% 2.26/1.35  tff(c_34, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.26/1.35  tff(c_32, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.26/1.35  tff(c_30, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.26/1.35  tff(c_28, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.26/1.35  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.26/1.35  tff(c_38, plain, (m1_orders_2('#skF_3', '#skF_2', '#skF_3') | k1_xboole_0='#skF_3'), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.26/1.35  tff(c_46, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_45, c_38])).
% 2.26/1.35  tff(c_8, plain, (![A_8]: (m1_orders_2(k1_xboole_0, A_8, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_8))) | ~l1_orders_2(A_8) | ~v5_orders_2(A_8) | ~v4_orders_2(A_8) | ~v3_orders_2(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.26/1.35  tff(c_54, plain, (![A_51]: (m1_orders_2('#skF_3', A_51, '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_orders_2(A_51) | ~v5_orders_2(A_51) | ~v4_orders_2(A_51) | ~v3_orders_2(A_51) | v2_struct_0(A_51))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_46, c_46, c_8])).
% 2.26/1.35  tff(c_57, plain, (m1_orders_2('#skF_3', '#skF_2', '#skF_3') | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_26, c_54])).
% 2.26/1.35  tff(c_60, plain, (m1_orders_2('#skF_3', '#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_28, c_57])).
% 2.26/1.35  tff(c_62, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_45, c_60])).
% 2.26/1.35  tff(c_63, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_44])).
% 2.26/1.35  tff(c_64, plain, (m1_orders_2('#skF_3', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_44])).
% 2.26/1.35  tff(c_18, plain, (![A_8, B_20, C_26]: (m1_subset_1('#skF_1'(A_8, B_20, C_26), u1_struct_0(A_8)) | ~m1_orders_2(C_26, A_8, B_20) | k1_xboole_0=B_20 | ~m1_subset_1(C_26, k1_zfmisc_1(u1_struct_0(A_8))) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_8))) | ~l1_orders_2(A_8) | ~v5_orders_2(A_8) | ~v4_orders_2(A_8) | ~v3_orders_2(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.26/1.35  tff(c_99, plain, (![A_78, B_79, C_80]: (k3_orders_2(A_78, B_79, '#skF_1'(A_78, B_79, C_80))=C_80 | ~m1_orders_2(C_80, A_78, B_79) | k1_xboole_0=B_79 | ~m1_subset_1(C_80, k1_zfmisc_1(u1_struct_0(A_78))) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_orders_2(A_78) | ~v5_orders_2(A_78) | ~v4_orders_2(A_78) | ~v3_orders_2(A_78) | v2_struct_0(A_78))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.26/1.35  tff(c_101, plain, (![B_79]: (k3_orders_2('#skF_2', B_79, '#skF_1'('#skF_2', B_79, '#skF_3'))='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', B_79) | k1_xboole_0=B_79 | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_26, c_99])).
% 2.26/1.35  tff(c_104, plain, (![B_79]: (k3_orders_2('#skF_2', B_79, '#skF_1'('#skF_2', B_79, '#skF_3'))='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', B_79) | k1_xboole_0=B_79 | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_28, c_101])).
% 2.26/1.35  tff(c_106, plain, (![B_81]: (k3_orders_2('#skF_2', B_81, '#skF_1'('#skF_2', B_81, '#skF_3'))='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', B_81) | k1_xboole_0=B_81 | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_36, c_104])).
% 2.26/1.35  tff(c_108, plain, (k3_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_3'))='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_26, c_106])).
% 2.26/1.35  tff(c_111, plain, (k3_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_3'))='#skF_3' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_108])).
% 2.26/1.35  tff(c_112, plain, (k3_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_63, c_111])).
% 2.26/1.35  tff(c_24, plain, (![A_30, B_38, C_42, D_44]: (r2_orders_2(A_30, B_38, C_42) | ~r2_hidden(B_38, k3_orders_2(A_30, D_44, C_42)) | ~m1_subset_1(D_44, k1_zfmisc_1(u1_struct_0(A_30))) | ~m1_subset_1(C_42, u1_struct_0(A_30)) | ~m1_subset_1(B_38, u1_struct_0(A_30)) | ~l1_orders_2(A_30) | ~v5_orders_2(A_30) | ~v4_orders_2(A_30) | ~v3_orders_2(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.26/1.35  tff(c_115, plain, (![B_38]: (r2_orders_2('#skF_2', B_38, '#skF_1'('#skF_2', '#skF_3', '#skF_3')) | ~r2_hidden(B_38, '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_112, c_24])).
% 2.26/1.35  tff(c_121, plain, (![B_38]: (r2_orders_2('#skF_2', B_38, '#skF_1'('#skF_2', '#skF_3', '#skF_3')) | ~r2_hidden(B_38, '#skF_3') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_28, c_26, c_115])).
% 2.26/1.35  tff(c_122, plain, (![B_38]: (r2_orders_2('#skF_2', B_38, '#skF_1'('#skF_2', '#skF_3', '#skF_3')) | ~r2_hidden(B_38, '#skF_3') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_36, c_121])).
% 2.26/1.35  tff(c_127, plain, (~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_122])).
% 2.26/1.35  tff(c_130, plain, (~m1_orders_2('#skF_3', '#skF_2', '#skF_3') | k1_xboole_0='#skF_3' | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_18, c_127])).
% 2.26/1.35  tff(c_133, plain, (k1_xboole_0='#skF_3' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_28, c_26, c_64, c_130])).
% 2.26/1.35  tff(c_135, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_63, c_133])).
% 2.26/1.35  tff(c_137, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_122])).
% 2.26/1.35  tff(c_79, plain, (![A_63, B_64, C_65]: (r2_hidden('#skF_1'(A_63, B_64, C_65), B_64) | ~m1_orders_2(C_65, A_63, B_64) | k1_xboole_0=B_64 | ~m1_subset_1(C_65, k1_zfmisc_1(u1_struct_0(A_63))) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_orders_2(A_63) | ~v5_orders_2(A_63) | ~v4_orders_2(A_63) | ~v3_orders_2(A_63) | v2_struct_0(A_63))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.26/1.35  tff(c_81, plain, (![B_64]: (r2_hidden('#skF_1'('#skF_2', B_64, '#skF_3'), B_64) | ~m1_orders_2('#skF_3', '#skF_2', B_64) | k1_xboole_0=B_64 | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_26, c_79])).
% 2.26/1.35  tff(c_84, plain, (![B_64]: (r2_hidden('#skF_1'('#skF_2', B_64, '#skF_3'), B_64) | ~m1_orders_2('#skF_3', '#skF_2', B_64) | k1_xboole_0=B_64 | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_28, c_81])).
% 2.26/1.35  tff(c_86, plain, (![B_66]: (r2_hidden('#skF_1'('#skF_2', B_66, '#skF_3'), B_66) | ~m1_orders_2('#skF_3', '#skF_2', B_66) | k1_xboole_0=B_66 | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_36, c_84])).
% 2.26/1.35  tff(c_88, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_3'), '#skF_3') | ~m1_orders_2('#skF_3', '#skF_2', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_26, c_86])).
% 2.26/1.35  tff(c_91, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_3'), '#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_88])).
% 2.26/1.35  tff(c_92, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_3'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_63, c_91])).
% 2.26/1.35  tff(c_143, plain, (![B_82]: (r2_orders_2('#skF_2', B_82, '#skF_1'('#skF_2', '#skF_3', '#skF_3')) | ~r2_hidden(B_82, '#skF_3') | ~m1_subset_1(B_82, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_122])).
% 2.26/1.35  tff(c_4, plain, (![A_1, C_7]: (~r2_orders_2(A_1, C_7, C_7) | ~m1_subset_1(C_7, u1_struct_0(A_1)) | ~l1_orders_2(A_1))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.26/1.35  tff(c_148, plain, (~l1_orders_2('#skF_2') | ~r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_3'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_3'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_143, c_4])).
% 2.26/1.35  tff(c_155, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_137, c_92, c_28, c_148])).
% 2.26/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.35  
% 2.26/1.35  Inference rules
% 2.26/1.35  ----------------------
% 2.26/1.35  #Ref     : 0
% 2.26/1.35  #Sup     : 17
% 2.26/1.35  #Fact    : 0
% 2.26/1.35  #Define  : 0
% 2.26/1.35  #Split   : 3
% 2.26/1.35  #Chain   : 0
% 2.26/1.35  #Close   : 0
% 2.26/1.35  
% 2.26/1.35  Ordering : KBO
% 2.26/1.35  
% 2.26/1.35  Simplification rules
% 2.26/1.35  ----------------------
% 2.26/1.35  #Subsume      : 0
% 2.26/1.35  #Demod        : 44
% 2.26/1.35  #Tautology    : 8
% 2.26/1.35  #SimpNegUnit  : 11
% 2.26/1.35  #BackRed      : 0
% 2.26/1.35  
% 2.26/1.35  #Partial instantiations: 0
% 2.26/1.35  #Strategies tried      : 1
% 2.26/1.35  
% 2.26/1.35  Timing (in seconds)
% 2.26/1.35  ----------------------
% 2.26/1.35  Preprocessing        : 0.34
% 2.26/1.35  Parsing              : 0.18
% 2.26/1.35  CNF conversion       : 0.03
% 2.26/1.35  Main loop            : 0.17
% 2.26/1.35  Inferencing          : 0.06
% 2.26/1.35  Reduction            : 0.05
% 2.26/1.35  Demodulation         : 0.03
% 2.26/1.35  BG Simplification    : 0.02
% 2.26/1.35  Subsumption          : 0.03
% 2.26/1.35  Abstraction          : 0.01
% 2.26/1.35  MUC search           : 0.00
% 2.26/1.35  Cooper               : 0.00
% 2.26/1.35  Total                : 0.55
% 2.26/1.35  Index Insertion      : 0.00
% 2.26/1.35  Index Deletion       : 0.00
% 2.26/1.35  Index Matching       : 0.00
% 2.26/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
