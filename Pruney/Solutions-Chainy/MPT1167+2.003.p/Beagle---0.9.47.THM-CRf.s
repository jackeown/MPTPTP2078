%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:51 EST 2020

% Result     : Theorem 10.53s
% Output     : CNFRefutation 10.53s
% Verified   : 
% Statistics : Number of formulae       :  211 (1819 expanded)
%              Number of leaves         :   29 ( 694 expanded)
%              Depth                    :   24
%              Number of atoms          :  834 (12585 expanded)
%              Number of equality atoms :   90 ( 747 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > m1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(f_196,negated_conjecture,(
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
                   => ! [E] :
                        ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(A)))
                       => ( ( r2_orders_2(A,B,C)
                            & r2_hidden(B,D)
                            & r2_hidden(C,E)
                            & m1_orders_2(E,A,D) )
                         => r2_hidden(B,E) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_orders_2)).

tff(f_77,axiom,(
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

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_138,axiom,(
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

tff(f_162,axiom,(
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
                 => ( r2_orders_2(A,B,C)
                   => r1_tarski(k3_orders_2(A,D,B),k3_orders_2(A,D,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_orders_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_34,plain,(
    ~ r2_hidden('#skF_3','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_38,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_36,plain,(
    m1_orders_2('#skF_6','#skF_2','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_58,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_56,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_54,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_52,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_44,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_5962,plain,(
    ! [A_521,B_522,C_523] :
      ( r2_hidden('#skF_1'(A_521,B_522,C_523),B_522)
      | ~ m1_orders_2(C_523,A_521,B_522)
      | k1_xboole_0 = B_522
      | ~ m1_subset_1(C_523,k1_zfmisc_1(u1_struct_0(A_521)))
      | ~ m1_subset_1(B_522,k1_zfmisc_1(u1_struct_0(A_521)))
      | ~ l1_orders_2(A_521)
      | ~ v5_orders_2(A_521)
      | ~ v4_orders_2(A_521)
      | ~ v3_orders_2(A_521)
      | v2_struct_0(A_521) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_5971,plain,(
    ! [B_522] :
      ( r2_hidden('#skF_1'('#skF_2',B_522,'#skF_6'),B_522)
      | ~ m1_orders_2('#skF_6','#skF_2',B_522)
      | k1_xboole_0 = B_522
      | ~ m1_subset_1(B_522,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_44,c_5962])).

tff(c_5982,plain,(
    ! [B_522] :
      ( r2_hidden('#skF_1'('#skF_2',B_522,'#skF_6'),B_522)
      | ~ m1_orders_2('#skF_6','#skF_2',B_522)
      | k1_xboole_0 = B_522
      | ~ m1_subset_1(B_522,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_5971])).

tff(c_5988,plain,(
    ! [B_524] :
      ( r2_hidden('#skF_1'('#skF_2',B_524,'#skF_6'),B_524)
      | ~ m1_orders_2('#skF_6','#skF_2',B_524)
      | k1_xboole_0 = B_524
      | ~ m1_subset_1(B_524,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_5982])).

tff(c_6000,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_5','#skF_6'),'#skF_5')
    | ~ m1_orders_2('#skF_6','#skF_2','#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_46,c_5988])).

tff(c_6010,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_5','#skF_6'),'#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_6000])).

tff(c_6011,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_6010])).

tff(c_62,plain,(
    ! [A_97,B_98] :
      ( r1_tarski(A_97,B_98)
      | ~ m1_subset_1(A_97,k1_zfmisc_1(B_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_74,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_46,c_62])).

tff(c_370,plain,(
    ! [A_170,B_171,C_172] :
      ( r2_hidden('#skF_1'(A_170,B_171,C_172),B_171)
      | ~ m1_orders_2(C_172,A_170,B_171)
      | k1_xboole_0 = B_171
      | ~ m1_subset_1(C_172,k1_zfmisc_1(u1_struct_0(A_170)))
      | ~ m1_subset_1(B_171,k1_zfmisc_1(u1_struct_0(A_170)))
      | ~ l1_orders_2(A_170)
      | ~ v5_orders_2(A_170)
      | ~ v4_orders_2(A_170)
      | ~ v3_orders_2(A_170)
      | v2_struct_0(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_377,plain,(
    ! [B_171] :
      ( r2_hidden('#skF_1'('#skF_2',B_171,'#skF_6'),B_171)
      | ~ m1_orders_2('#skF_6','#skF_2',B_171)
      | k1_xboole_0 = B_171
      | ~ m1_subset_1(B_171,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_44,c_370])).

tff(c_384,plain,(
    ! [B_171] :
      ( r2_hidden('#skF_1'('#skF_2',B_171,'#skF_6'),B_171)
      | ~ m1_orders_2('#skF_6','#skF_2',B_171)
      | k1_xboole_0 = B_171
      | ~ m1_subset_1(B_171,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_377])).

tff(c_390,plain,(
    ! [B_173] :
      ( r2_hidden('#skF_1'('#skF_2',B_173,'#skF_6'),B_173)
      | ~ m1_orders_2('#skF_6','#skF_2',B_173)
      | k1_xboole_0 = B_173
      | ~ m1_subset_1(B_173,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_384])).

tff(c_400,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_5','#skF_6'),'#skF_5')
    | ~ m1_orders_2('#skF_6','#skF_2','#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_46,c_390])).

tff(c_409,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_5','#skF_6'),'#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_400])).

tff(c_410,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_409])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_248,plain,(
    ! [C_139,A_140] :
      ( k1_xboole_0 = C_139
      | ~ m1_orders_2(C_139,A_140,k1_xboole_0)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ l1_orders_2(A_140)
      | ~ v5_orders_2(A_140)
      | ~ v4_orders_2(A_140)
      | ~ v3_orders_2(A_140)
      | v2_struct_0(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_253,plain,
    ( k1_xboole_0 = '#skF_6'
    | ~ m1_orders_2('#skF_6','#skF_2',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_248])).

tff(c_259,plain,
    ( k1_xboole_0 = '#skF_6'
    | ~ m1_orders_2('#skF_6','#skF_2',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_253])).

tff(c_260,plain,
    ( k1_xboole_0 = '#skF_6'
    | ~ m1_orders_2('#skF_6','#skF_2',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_259])).

tff(c_265,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_260])).

tff(c_270,plain,(
    ~ r1_tarski(k1_xboole_0,u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_6,c_265])).

tff(c_415,plain,(
    ~ r1_tarski('#skF_5',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_410,c_270])).

tff(c_422,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_415])).

tff(c_424,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_409])).

tff(c_20,plain,(
    ! [A_10,B_22,C_28] :
      ( m1_subset_1('#skF_1'(A_10,B_22,C_28),u1_struct_0(A_10))
      | ~ m1_orders_2(C_28,A_10,B_22)
      | k1_xboole_0 = B_22
      | ~ m1_subset_1(C_28,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_orders_2(A_10)
      | ~ v5_orders_2(A_10)
      | ~ v4_orders_2(A_10)
      | ~ v3_orders_2(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_686,plain,(
    ! [A_206,B_207,C_208] :
      ( k3_orders_2(A_206,B_207,'#skF_1'(A_206,B_207,C_208)) = C_208
      | ~ m1_orders_2(C_208,A_206,B_207)
      | k1_xboole_0 = B_207
      | ~ m1_subset_1(C_208,k1_zfmisc_1(u1_struct_0(A_206)))
      | ~ m1_subset_1(B_207,k1_zfmisc_1(u1_struct_0(A_206)))
      | ~ l1_orders_2(A_206)
      | ~ v5_orders_2(A_206)
      | ~ v4_orders_2(A_206)
      | ~ v3_orders_2(A_206)
      | v2_struct_0(A_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_696,plain,(
    ! [B_207] :
      ( k3_orders_2('#skF_2',B_207,'#skF_1'('#skF_2',B_207,'#skF_6')) = '#skF_6'
      | ~ m1_orders_2('#skF_6','#skF_2',B_207)
      | k1_xboole_0 = B_207
      | ~ m1_subset_1(B_207,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_44,c_686])).

tff(c_704,plain,(
    ! [B_207] :
      ( k3_orders_2('#skF_2',B_207,'#skF_1'('#skF_2',B_207,'#skF_6')) = '#skF_6'
      | ~ m1_orders_2('#skF_6','#skF_2',B_207)
      | k1_xboole_0 = B_207
      | ~ m1_subset_1(B_207,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_696])).

tff(c_711,plain,(
    ! [B_209] :
      ( k3_orders_2('#skF_2',B_209,'#skF_1'('#skF_2',B_209,'#skF_6')) = '#skF_6'
      | ~ m1_orders_2('#skF_6','#skF_2',B_209)
      | k1_xboole_0 = B_209
      | ~ m1_subset_1(B_209,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_704])).

tff(c_724,plain,
    ( k3_orders_2('#skF_2','#skF_5','#skF_1'('#skF_2','#skF_5','#skF_6')) = '#skF_6'
    | ~ m1_orders_2('#skF_6','#skF_2','#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_46,c_711])).

tff(c_734,plain,
    ( k3_orders_2('#skF_2','#skF_5','#skF_1'('#skF_2','#skF_5','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_724])).

tff(c_735,plain,(
    k3_orders_2('#skF_2','#skF_5','#skF_1'('#skF_2','#skF_5','#skF_6')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_424,c_734])).

tff(c_28,plain,(
    ! [B_47,D_53,A_39,C_51] :
      ( r2_hidden(B_47,D_53)
      | ~ r2_hidden(B_47,k3_orders_2(A_39,D_53,C_51))
      | ~ m1_subset_1(D_53,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ m1_subset_1(C_51,u1_struct_0(A_39))
      | ~ m1_subset_1(B_47,u1_struct_0(A_39))
      | ~ l1_orders_2(A_39)
      | ~ v5_orders_2(A_39)
      | ~ v4_orders_2(A_39)
      | ~ v3_orders_2(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_749,plain,(
    ! [B_47] :
      ( r2_hidden(B_47,'#skF_5')
      | ~ r2_hidden(B_47,'#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_47,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_735,c_28])).

tff(c_776,plain,(
    ! [B_47] :
      ( r2_hidden(B_47,'#skF_5')
      | ~ r2_hidden(B_47,'#skF_6')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_47,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_46,c_749])).

tff(c_777,plain,(
    ! [B_47] :
      ( r2_hidden(B_47,'#skF_5')
      | ~ r2_hidden(B_47,'#skF_6')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_47,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_776])).

tff(c_885,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_777])).

tff(c_888,plain,
    ( ~ m1_orders_2('#skF_6','#skF_2','#skF_5')
    | k1_xboole_0 = '#skF_5'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_885])).

tff(c_900,plain,
    ( k1_xboole_0 = '#skF_5'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_46,c_44,c_36,c_888])).

tff(c_902,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_424,c_900])).

tff(c_904,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_777])).

tff(c_30,plain,(
    ! [A_39,B_47,C_51,D_53] :
      ( r2_orders_2(A_39,B_47,C_51)
      | ~ r2_hidden(B_47,k3_orders_2(A_39,D_53,C_51))
      | ~ m1_subset_1(D_53,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ m1_subset_1(C_51,u1_struct_0(A_39))
      | ~ m1_subset_1(B_47,u1_struct_0(A_39))
      | ~ l1_orders_2(A_39)
      | ~ v5_orders_2(A_39)
      | ~ v4_orders_2(A_39)
      | ~ v3_orders_2(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_741,plain,(
    ! [B_47] :
      ( r2_orders_2('#skF_2',B_47,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ r2_hidden(B_47,'#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_47,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_735,c_30])).

tff(c_769,plain,(
    ! [B_47] :
      ( r2_orders_2('#skF_2',B_47,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ r2_hidden(B_47,'#skF_6')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_47,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_46,c_741])).

tff(c_770,plain,(
    ! [B_47] :
      ( r2_orders_2('#skF_2',B_47,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ r2_hidden(B_47,'#skF_6')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_47,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_769])).

tff(c_1417,plain,(
    ! [B_269] :
      ( r2_orders_2('#skF_2',B_269,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ r2_hidden(B_269,'#skF_6')
      | ~ m1_subset_1(B_269,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_904,c_770])).

tff(c_1002,plain,(
    ! [A_225,D_226,B_227,C_228] :
      ( r1_tarski(k3_orders_2(A_225,D_226,B_227),k3_orders_2(A_225,D_226,C_228))
      | ~ r2_orders_2(A_225,B_227,C_228)
      | ~ m1_subset_1(D_226,k1_zfmisc_1(u1_struct_0(A_225)))
      | ~ m1_subset_1(C_228,u1_struct_0(A_225))
      | ~ m1_subset_1(B_227,u1_struct_0(A_225))
      | ~ l1_orders_2(A_225)
      | ~ v5_orders_2(A_225)
      | ~ v4_orders_2(A_225)
      | ~ v3_orders_2(A_225)
      | v2_struct_0(A_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_1018,plain,(
    ! [B_227] :
      ( r1_tarski(k3_orders_2('#skF_2','#skF_5',B_227),'#skF_6')
      | ~ r2_orders_2('#skF_2',B_227,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_227,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_735,c_1002])).

tff(c_1028,plain,(
    ! [B_227] :
      ( r1_tarski(k3_orders_2('#skF_2','#skF_5',B_227),'#skF_6')
      | ~ r2_orders_2('#skF_2',B_227,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ m1_subset_1(B_227,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_904,c_46,c_1018])).

tff(c_1029,plain,(
    ! [B_227] :
      ( r1_tarski(k3_orders_2('#skF_2','#skF_5',B_227),'#skF_6')
      | ~ r2_orders_2('#skF_2',B_227,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ m1_subset_1(B_227,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1028])).

tff(c_1429,plain,(
    ! [B_269] :
      ( r1_tarski(k3_orders_2('#skF_2','#skF_5',B_269),'#skF_6')
      | ~ r2_hidden(B_269,'#skF_6')
      | ~ m1_subset_1(B_269,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_1417,c_1029])).

tff(c_50,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_40,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_42,plain,(
    r2_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_861,plain,(
    ! [B_216,A_217,D_218,C_219] :
      ( r2_hidden(B_216,k3_orders_2(A_217,D_218,C_219))
      | ~ r2_hidden(B_216,D_218)
      | ~ r2_orders_2(A_217,B_216,C_219)
      | ~ m1_subset_1(D_218,k1_zfmisc_1(u1_struct_0(A_217)))
      | ~ m1_subset_1(C_219,u1_struct_0(A_217))
      | ~ m1_subset_1(B_216,u1_struct_0(A_217))
      | ~ l1_orders_2(A_217)
      | ~ v5_orders_2(A_217)
      | ~ v4_orders_2(A_217)
      | ~ v3_orders_2(A_217)
      | v2_struct_0(A_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_873,plain,(
    ! [B_216,C_219] :
      ( r2_hidden(B_216,k3_orders_2('#skF_2','#skF_5',C_219))
      | ~ r2_hidden(B_216,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_216,C_219)
      | ~ m1_subset_1(C_219,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_216,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_46,c_861])).

tff(c_883,plain,(
    ! [B_216,C_219] :
      ( r2_hidden(B_216,k3_orders_2('#skF_2','#skF_5',C_219))
      | ~ r2_hidden(B_216,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_216,C_219)
      | ~ m1_subset_1(C_219,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_216,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_873])).

tff(c_1242,plain,(
    ! [B_256,C_257] :
      ( r2_hidden(B_256,k3_orders_2('#skF_2','#skF_5',C_257))
      | ~ r2_hidden(B_256,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_256,C_257)
      | ~ m1_subset_1(C_257,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_256,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_883])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( r2_hidden(C_4,A_1)
      | ~ r2_hidden(C_4,B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4220,plain,(
    ! [B_438,A_439,C_440] :
      ( r2_hidden(B_438,A_439)
      | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5',C_440),k1_zfmisc_1(A_439))
      | ~ r2_hidden(B_438,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_438,C_440)
      | ~ m1_subset_1(C_440,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_438,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_1242,c_2])).

tff(c_5794,plain,(
    ! [B_508,B_509,C_510] :
      ( r2_hidden(B_508,B_509)
      | ~ r2_hidden(B_508,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_508,C_510)
      | ~ m1_subset_1(C_510,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_508,u1_struct_0('#skF_2'))
      | ~ r1_tarski(k3_orders_2('#skF_2','#skF_5',C_510),B_509) ) ),
    inference(resolution,[status(thm)],[c_6,c_4220])).

tff(c_5798,plain,(
    ! [B_509] :
      ( r2_hidden('#skF_3',B_509)
      | ~ r2_hidden('#skF_3','#skF_5')
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ r1_tarski(k3_orders_2('#skF_2','#skF_5','#skF_4'),B_509) ) ),
    inference(resolution,[status(thm)],[c_42,c_5794])).

tff(c_5805,plain,(
    ! [B_511] :
      ( r2_hidden('#skF_3',B_511)
      | ~ r1_tarski(k3_orders_2('#skF_2','#skF_5','#skF_4'),B_511) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_40,c_5798])).

tff(c_5817,plain,
    ( r2_hidden('#skF_3','#skF_6')
    | ~ r2_hidden('#skF_4','#skF_6')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_1429,c_5805])).

tff(c_5834,plain,(
    r2_hidden('#skF_3','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_38,c_5817])).

tff(c_5836,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_5834])).

tff(c_5837,plain,
    ( ~ m1_orders_2('#skF_6','#skF_2',k1_xboole_0)
    | k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_260])).

tff(c_5910,plain,(
    ~ m1_orders_2('#skF_6','#skF_2',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_5837])).

tff(c_6019,plain,(
    ~ m1_orders_2('#skF_6','#skF_2','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6011,c_5910])).

tff(c_6028,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_6019])).

tff(c_6030,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_6010])).

tff(c_6224,plain,(
    ! [A_545,B_546,C_547] :
      ( k3_orders_2(A_545,B_546,'#skF_1'(A_545,B_546,C_547)) = C_547
      | ~ m1_orders_2(C_547,A_545,B_546)
      | k1_xboole_0 = B_546
      | ~ m1_subset_1(C_547,k1_zfmisc_1(u1_struct_0(A_545)))
      | ~ m1_subset_1(B_546,k1_zfmisc_1(u1_struct_0(A_545)))
      | ~ l1_orders_2(A_545)
      | ~ v5_orders_2(A_545)
      | ~ v4_orders_2(A_545)
      | ~ v3_orders_2(A_545)
      | v2_struct_0(A_545) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_6236,plain,(
    ! [B_546] :
      ( k3_orders_2('#skF_2',B_546,'#skF_1'('#skF_2',B_546,'#skF_6')) = '#skF_6'
      | ~ m1_orders_2('#skF_6','#skF_2',B_546)
      | k1_xboole_0 = B_546
      | ~ m1_subset_1(B_546,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_44,c_6224])).

tff(c_6248,plain,(
    ! [B_546] :
      ( k3_orders_2('#skF_2',B_546,'#skF_1'('#skF_2',B_546,'#skF_6')) = '#skF_6'
      | ~ m1_orders_2('#skF_6','#skF_2',B_546)
      | k1_xboole_0 = B_546
      | ~ m1_subset_1(B_546,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_6236])).

tff(c_6301,plain,(
    ! [B_553] :
      ( k3_orders_2('#skF_2',B_553,'#skF_1'('#skF_2',B_553,'#skF_6')) = '#skF_6'
      | ~ m1_orders_2('#skF_6','#skF_2',B_553)
      | k1_xboole_0 = B_553
      | ~ m1_subset_1(B_553,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_6248])).

tff(c_6316,plain,
    ( k3_orders_2('#skF_2','#skF_5','#skF_1'('#skF_2','#skF_5','#skF_6')) = '#skF_6'
    | ~ m1_orders_2('#skF_6','#skF_2','#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_46,c_6301])).

tff(c_6327,plain,
    ( k3_orders_2('#skF_2','#skF_5','#skF_1'('#skF_2','#skF_5','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_6316])).

tff(c_6328,plain,(
    k3_orders_2('#skF_2','#skF_5','#skF_1'('#skF_2','#skF_5','#skF_6')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_6030,c_6327])).

tff(c_6333,plain,(
    ! [B_47] :
      ( r2_hidden(B_47,'#skF_5')
      | ~ r2_hidden(B_47,'#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_47,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6328,c_28])).

tff(c_6343,plain,(
    ! [B_47] :
      ( r2_hidden(B_47,'#skF_5')
      | ~ r2_hidden(B_47,'#skF_6')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_47,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_46,c_6333])).

tff(c_6344,plain,(
    ! [B_47] :
      ( r2_hidden(B_47,'#skF_5')
      | ~ r2_hidden(B_47,'#skF_6')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_47,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_6343])).

tff(c_6406,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_6344])).

tff(c_6409,plain,
    ( ~ m1_orders_2('#skF_6','#skF_2','#skF_5')
    | k1_xboole_0 = '#skF_5'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_6406])).

tff(c_6424,plain,
    ( k1_xboole_0 = '#skF_5'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_46,c_44,c_36,c_6409])).

tff(c_6426,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_6030,c_6424])).

tff(c_6428,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_6344])).

tff(c_6331,plain,(
    ! [B_47] :
      ( r2_orders_2('#skF_2',B_47,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ r2_hidden(B_47,'#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_47,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6328,c_30])).

tff(c_6340,plain,(
    ! [B_47] :
      ( r2_orders_2('#skF_2',B_47,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ r2_hidden(B_47,'#skF_6')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_47,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_46,c_6331])).

tff(c_6341,plain,(
    ! [B_47] :
      ( r2_orders_2('#skF_2',B_47,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ r2_hidden(B_47,'#skF_6')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_47,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_6340])).

tff(c_7317,plain,(
    ! [B_47] :
      ( r2_orders_2('#skF_2',B_47,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ r2_hidden(B_47,'#skF_6')
      | ~ m1_subset_1(B_47,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6428,c_6341])).

tff(c_6376,plain,(
    ! [A_558,D_559,B_560,C_561] :
      ( r1_tarski(k3_orders_2(A_558,D_559,B_560),k3_orders_2(A_558,D_559,C_561))
      | ~ r2_orders_2(A_558,B_560,C_561)
      | ~ m1_subset_1(D_559,k1_zfmisc_1(u1_struct_0(A_558)))
      | ~ m1_subset_1(C_561,u1_struct_0(A_558))
      | ~ m1_subset_1(B_560,u1_struct_0(A_558))
      | ~ l1_orders_2(A_558)
      | ~ v5_orders_2(A_558)
      | ~ v4_orders_2(A_558)
      | ~ v3_orders_2(A_558)
      | v2_struct_0(A_558) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_6392,plain,(
    ! [B_560] :
      ( r1_tarski(k3_orders_2('#skF_2','#skF_5',B_560),'#skF_6')
      | ~ r2_orders_2('#skF_2',B_560,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_560,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6328,c_6376])).

tff(c_6402,plain,(
    ! [B_560] :
      ( r1_tarski(k3_orders_2('#skF_2','#skF_5',B_560),'#skF_6')
      | ~ r2_orders_2('#skF_2',B_560,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_560,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_46,c_6392])).

tff(c_6403,plain,(
    ! [B_560] :
      ( r1_tarski(k3_orders_2('#skF_2','#skF_5',B_560),'#skF_6')
      | ~ r2_orders_2('#skF_2',B_560,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_560,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_6402])).

tff(c_8311,plain,(
    ! [B_687] :
      ( r1_tarski(k3_orders_2('#skF_2','#skF_5',B_687),'#skF_6')
      | ~ r2_orders_2('#skF_2',B_687,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ m1_subset_1(B_687,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6428,c_6403])).

tff(c_8315,plain,(
    ! [B_47] :
      ( r1_tarski(k3_orders_2('#skF_2','#skF_5',B_47),'#skF_6')
      | ~ r2_hidden(B_47,'#skF_6')
      | ~ m1_subset_1(B_47,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_7317,c_8311])).

tff(c_6473,plain,(
    ! [B_563,A_564,D_565,C_566] :
      ( r2_hidden(B_563,k3_orders_2(A_564,D_565,C_566))
      | ~ r2_hidden(B_563,D_565)
      | ~ r2_orders_2(A_564,B_563,C_566)
      | ~ m1_subset_1(D_565,k1_zfmisc_1(u1_struct_0(A_564)))
      | ~ m1_subset_1(C_566,u1_struct_0(A_564))
      | ~ m1_subset_1(B_563,u1_struct_0(A_564))
      | ~ l1_orders_2(A_564)
      | ~ v5_orders_2(A_564)
      | ~ v4_orders_2(A_564)
      | ~ v3_orders_2(A_564)
      | v2_struct_0(A_564) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_6487,plain,(
    ! [B_563,C_566] :
      ( r2_hidden(B_563,k3_orders_2('#skF_2','#skF_5',C_566))
      | ~ r2_hidden(B_563,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_563,C_566)
      | ~ m1_subset_1(C_566,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_563,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_46,c_6473])).

tff(c_6501,plain,(
    ! [B_563,C_566] :
      ( r2_hidden(B_563,k3_orders_2('#skF_2','#skF_5',C_566))
      | ~ r2_hidden(B_563,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_563,C_566)
      | ~ m1_subset_1(C_566,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_563,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_6487])).

tff(c_6816,plain,(
    ! [B_602,C_603] :
      ( r2_hidden(B_602,k3_orders_2('#skF_2','#skF_5',C_603))
      | ~ r2_hidden(B_602,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_602,C_603)
      | ~ m1_subset_1(C_603,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_602,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_6501])).

tff(c_9269,plain,(
    ! [B_786,A_787,C_788] :
      ( r2_hidden(B_786,A_787)
      | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5',C_788),k1_zfmisc_1(A_787))
      | ~ r2_hidden(B_786,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_786,C_788)
      | ~ m1_subset_1(C_788,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_786,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_6816,c_2])).

tff(c_10557,plain,(
    ! [B_857,B_858,C_859] :
      ( r2_hidden(B_857,B_858)
      | ~ r2_hidden(B_857,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_857,C_859)
      | ~ m1_subset_1(C_859,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_857,u1_struct_0('#skF_2'))
      | ~ r1_tarski(k3_orders_2('#skF_2','#skF_5',C_859),B_858) ) ),
    inference(resolution,[status(thm)],[c_6,c_9269])).

tff(c_10561,plain,(
    ! [B_858] :
      ( r2_hidden('#skF_3',B_858)
      | ~ r2_hidden('#skF_3','#skF_5')
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ r1_tarski(k3_orders_2('#skF_2','#skF_5','#skF_4'),B_858) ) ),
    inference(resolution,[status(thm)],[c_42,c_10557])).

tff(c_10568,plain,(
    ! [B_860] :
      ( r2_hidden('#skF_3',B_860)
      | ~ r1_tarski(k3_orders_2('#skF_2','#skF_5','#skF_4'),B_860) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_40,c_10561])).

tff(c_10572,plain,
    ( r2_hidden('#skF_3','#skF_6')
    | ~ r2_hidden('#skF_4','#skF_6')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_8315,c_10568])).

tff(c_10587,plain,(
    r2_hidden('#skF_3','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_38,c_10572])).

tff(c_10589,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_10587])).

tff(c_10590,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_5837])).

tff(c_10591,plain,(
    m1_orders_2('#skF_6','#skF_2',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_5837])).

tff(c_10607,plain,(
    m1_orders_2('#skF_6','#skF_2','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10590,c_10591])).

tff(c_18,plain,(
    ! [A_10,B_22,C_28] :
      ( r2_hidden('#skF_1'(A_10,B_22,C_28),B_22)
      | ~ m1_orders_2(C_28,A_10,B_22)
      | k1_xboole_0 = B_22
      | ~ m1_subset_1(C_28,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_orders_2(A_10)
      | ~ v5_orders_2(A_10)
      | ~ v4_orders_2(A_10)
      | ~ v3_orders_2(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_10618,plain,(
    ! [A_861,B_862,C_863] :
      ( r2_hidden('#skF_1'(A_861,B_862,C_863),B_862)
      | ~ m1_orders_2(C_863,A_861,B_862)
      | B_862 = '#skF_6'
      | ~ m1_subset_1(C_863,k1_zfmisc_1(u1_struct_0(A_861)))
      | ~ m1_subset_1(B_862,k1_zfmisc_1(u1_struct_0(A_861)))
      | ~ l1_orders_2(A_861)
      | ~ v5_orders_2(A_861)
      | ~ v4_orders_2(A_861)
      | ~ v3_orders_2(A_861)
      | v2_struct_0(A_861) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10590,c_18])).

tff(c_10625,plain,(
    ! [B_862] :
      ( r2_hidden('#skF_1'('#skF_2',B_862,'#skF_6'),B_862)
      | ~ m1_orders_2('#skF_6','#skF_2',B_862)
      | B_862 = '#skF_6'
      | ~ m1_subset_1(B_862,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_44,c_10618])).

tff(c_10632,plain,(
    ! [B_862] :
      ( r2_hidden('#skF_1'('#skF_2',B_862,'#skF_6'),B_862)
      | ~ m1_orders_2('#skF_6','#skF_2',B_862)
      | B_862 = '#skF_6'
      | ~ m1_subset_1(B_862,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_10625])).

tff(c_10638,plain,(
    ! [B_864] :
      ( r2_hidden('#skF_1'('#skF_2',B_864,'#skF_6'),B_864)
      | ~ m1_orders_2('#skF_6','#skF_2',B_864)
      | B_864 = '#skF_6'
      | ~ m1_subset_1(B_864,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_10632])).

tff(c_10648,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_5','#skF_6'),'#skF_5')
    | ~ m1_orders_2('#skF_6','#skF_2','#skF_5')
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_46,c_10638])).

tff(c_10660,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_5','#skF_6'),'#skF_5')
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_10648])).

tff(c_10661,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_10660])).

tff(c_5838,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_260])).

tff(c_255,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ m1_orders_2('#skF_5','#skF_2',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_248])).

tff(c_263,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ m1_orders_2('#skF_5','#skF_2',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_255])).

tff(c_264,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ m1_orders_2('#skF_5','#skF_2',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_263])).

tff(c_10593,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ m1_orders_2('#skF_5','#skF_2',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5838,c_264])).

tff(c_10594,plain,(
    ~ m1_orders_2('#skF_5','#skF_2',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_10593])).

tff(c_10614,plain,(
    ~ m1_orders_2('#skF_5','#skF_2','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10590,c_10594])).

tff(c_10662,plain,(
    ~ m1_orders_2('#skF_6','#skF_2','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10661,c_10614])).

tff(c_10677,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10607,c_10662])).

tff(c_10679,plain,(
    '#skF_5' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_10660])).

tff(c_10851,plain,(
    ! [A_10,B_22,C_28] :
      ( m1_subset_1('#skF_1'(A_10,B_22,C_28),u1_struct_0(A_10))
      | ~ m1_orders_2(C_28,A_10,B_22)
      | B_22 = '#skF_6'
      | ~ m1_subset_1(C_28,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_orders_2(A_10)
      | ~ v5_orders_2(A_10)
      | ~ v4_orders_2(A_10)
      | ~ v3_orders_2(A_10)
      | v2_struct_0(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10590,c_20])).

tff(c_16,plain,(
    ! [A_10,B_22,C_28] :
      ( k3_orders_2(A_10,B_22,'#skF_1'(A_10,B_22,C_28)) = C_28
      | ~ m1_orders_2(C_28,A_10,B_22)
      | k1_xboole_0 = B_22
      | ~ m1_subset_1(C_28,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_orders_2(A_10)
      | ~ v5_orders_2(A_10)
      | ~ v4_orders_2(A_10)
      | ~ v3_orders_2(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_10920,plain,(
    ! [A_897,B_898,C_899] :
      ( k3_orders_2(A_897,B_898,'#skF_1'(A_897,B_898,C_899)) = C_899
      | ~ m1_orders_2(C_899,A_897,B_898)
      | B_898 = '#skF_6'
      | ~ m1_subset_1(C_899,k1_zfmisc_1(u1_struct_0(A_897)))
      | ~ m1_subset_1(B_898,k1_zfmisc_1(u1_struct_0(A_897)))
      | ~ l1_orders_2(A_897)
      | ~ v5_orders_2(A_897)
      | ~ v4_orders_2(A_897)
      | ~ v3_orders_2(A_897)
      | v2_struct_0(A_897) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10590,c_16])).

tff(c_10930,plain,(
    ! [B_898] :
      ( k3_orders_2('#skF_2',B_898,'#skF_1'('#skF_2',B_898,'#skF_6')) = '#skF_6'
      | ~ m1_orders_2('#skF_6','#skF_2',B_898)
      | B_898 = '#skF_6'
      | ~ m1_subset_1(B_898,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_44,c_10920])).

tff(c_10938,plain,(
    ! [B_898] :
      ( k3_orders_2('#skF_2',B_898,'#skF_1'('#skF_2',B_898,'#skF_6')) = '#skF_6'
      | ~ m1_orders_2('#skF_6','#skF_2',B_898)
      | B_898 = '#skF_6'
      | ~ m1_subset_1(B_898,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_10930])).

tff(c_10962,plain,(
    ! [B_904] :
      ( k3_orders_2('#skF_2',B_904,'#skF_1'('#skF_2',B_904,'#skF_6')) = '#skF_6'
      | ~ m1_orders_2('#skF_6','#skF_2',B_904)
      | B_904 = '#skF_6'
      | ~ m1_subset_1(B_904,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_10938])).

tff(c_10975,plain,
    ( k3_orders_2('#skF_2','#skF_5','#skF_1'('#skF_2','#skF_5','#skF_6')) = '#skF_6'
    | ~ m1_orders_2('#skF_6','#skF_2','#skF_5')
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_46,c_10962])).

tff(c_10988,plain,
    ( k3_orders_2('#skF_2','#skF_5','#skF_1'('#skF_2','#skF_5','#skF_6')) = '#skF_6'
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_10975])).

tff(c_10989,plain,(
    k3_orders_2('#skF_2','#skF_5','#skF_1'('#skF_2','#skF_5','#skF_6')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_10679,c_10988])).

tff(c_11006,plain,(
    ! [B_47] :
      ( r2_hidden(B_47,'#skF_5')
      | ~ r2_hidden(B_47,'#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_47,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10989,c_28])).

tff(c_11024,plain,(
    ! [B_47] :
      ( r2_hidden(B_47,'#skF_5')
      | ~ r2_hidden(B_47,'#skF_6')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_47,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_46,c_11006])).

tff(c_11025,plain,(
    ! [B_47] :
      ( r2_hidden(B_47,'#skF_5')
      | ~ r2_hidden(B_47,'#skF_6')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_47,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_11024])).

tff(c_11068,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_11025])).

tff(c_11071,plain,
    ( ~ m1_orders_2('#skF_6','#skF_2','#skF_5')
    | '#skF_5' = '#skF_6'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_10851,c_11068])).

tff(c_11083,plain,
    ( '#skF_5' = '#skF_6'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_46,c_44,c_36,c_11071])).

tff(c_11085,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_10679,c_11083])).

tff(c_11087,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_11025])).

tff(c_10998,plain,(
    ! [B_47] :
      ( r2_orders_2('#skF_2',B_47,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ r2_hidden(B_47,'#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_47,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10989,c_30])).

tff(c_11017,plain,(
    ! [B_47] :
      ( r2_orders_2('#skF_2',B_47,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ r2_hidden(B_47,'#skF_6')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_47,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_46,c_10998])).

tff(c_11018,plain,(
    ! [B_47] :
      ( r2_orders_2('#skF_2',B_47,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ r2_hidden(B_47,'#skF_6')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_47,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_11017])).

tff(c_11571,plain,(
    ! [B_961] :
      ( r2_orders_2('#skF_2',B_961,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ r2_hidden(B_961,'#skF_6')
      | ~ m1_subset_1(B_961,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11087,c_11018])).

tff(c_11228,plain,(
    ! [A_919,D_920,B_921,C_922] :
      ( r1_tarski(k3_orders_2(A_919,D_920,B_921),k3_orders_2(A_919,D_920,C_922))
      | ~ r2_orders_2(A_919,B_921,C_922)
      | ~ m1_subset_1(D_920,k1_zfmisc_1(u1_struct_0(A_919)))
      | ~ m1_subset_1(C_922,u1_struct_0(A_919))
      | ~ m1_subset_1(B_921,u1_struct_0(A_919))
      | ~ l1_orders_2(A_919)
      | ~ v5_orders_2(A_919)
      | ~ v4_orders_2(A_919)
      | ~ v3_orders_2(A_919)
      | v2_struct_0(A_919) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_11244,plain,(
    ! [B_921] :
      ( r1_tarski(k3_orders_2('#skF_2','#skF_5',B_921),'#skF_6')
      | ~ r2_orders_2('#skF_2',B_921,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_921,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10989,c_11228])).

tff(c_11254,plain,(
    ! [B_921] :
      ( r1_tarski(k3_orders_2('#skF_2','#skF_5',B_921),'#skF_6')
      | ~ r2_orders_2('#skF_2',B_921,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ m1_subset_1(B_921,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_11087,c_46,c_11244])).

tff(c_11255,plain,(
    ! [B_921] :
      ( r1_tarski(k3_orders_2('#skF_2','#skF_5',B_921),'#skF_6')
      | ~ r2_orders_2('#skF_2',B_921,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ m1_subset_1(B_921,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_11254])).

tff(c_11583,plain,(
    ! [B_961] :
      ( r1_tarski(k3_orders_2('#skF_2','#skF_5',B_961),'#skF_6')
      | ~ r2_hidden(B_961,'#skF_6')
      | ~ m1_subset_1(B_961,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_11571,c_11255])).

tff(c_11088,plain,(
    ! [B_907,A_908,D_909,C_910] :
      ( r2_hidden(B_907,k3_orders_2(A_908,D_909,C_910))
      | ~ r2_hidden(B_907,D_909)
      | ~ r2_orders_2(A_908,B_907,C_910)
      | ~ m1_subset_1(D_909,k1_zfmisc_1(u1_struct_0(A_908)))
      | ~ m1_subset_1(C_910,u1_struct_0(A_908))
      | ~ m1_subset_1(B_907,u1_struct_0(A_908))
      | ~ l1_orders_2(A_908)
      | ~ v5_orders_2(A_908)
      | ~ v4_orders_2(A_908)
      | ~ v3_orders_2(A_908)
      | v2_struct_0(A_908) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_11100,plain,(
    ! [B_907,C_910] :
      ( r2_hidden(B_907,k3_orders_2('#skF_2','#skF_5',C_910))
      | ~ r2_hidden(B_907,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_907,C_910)
      | ~ m1_subset_1(C_910,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_907,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_46,c_11088])).

tff(c_11110,plain,(
    ! [B_907,C_910] :
      ( r2_hidden(B_907,k3_orders_2('#skF_2','#skF_5',C_910))
      | ~ r2_hidden(B_907,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_907,C_910)
      | ~ m1_subset_1(C_910,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_907,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_11100])).

tff(c_11460,plain,(
    ! [B_949,C_950] :
      ( r2_hidden(B_949,k3_orders_2('#skF_2','#skF_5',C_950))
      | ~ r2_hidden(B_949,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_949,C_950)
      | ~ m1_subset_1(C_950,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_949,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_11110])).

tff(c_12496,plain,(
    ! [B_1067,A_1068,C_1069] :
      ( r2_hidden(B_1067,A_1068)
      | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5',C_1069),k1_zfmisc_1(A_1068))
      | ~ r2_hidden(B_1067,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_1067,C_1069)
      | ~ m1_subset_1(C_1069,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_1067,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_11460,c_2])).

tff(c_12750,plain,(
    ! [B_1090,B_1091,C_1092] :
      ( r2_hidden(B_1090,B_1091)
      | ~ r2_hidden(B_1090,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_1090,C_1092)
      | ~ m1_subset_1(C_1092,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_1090,u1_struct_0('#skF_2'))
      | ~ r1_tarski(k3_orders_2('#skF_2','#skF_5',C_1092),B_1091) ) ),
    inference(resolution,[status(thm)],[c_6,c_12496])).

tff(c_12754,plain,(
    ! [B_1091] :
      ( r2_hidden('#skF_3',B_1091)
      | ~ r2_hidden('#skF_3','#skF_5')
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ r1_tarski(k3_orders_2('#skF_2','#skF_5','#skF_4'),B_1091) ) ),
    inference(resolution,[status(thm)],[c_42,c_12750])).

tff(c_12761,plain,(
    ! [B_1093] :
      ( r2_hidden('#skF_3',B_1093)
      | ~ r1_tarski(k3_orders_2('#skF_2','#skF_5','#skF_4'),B_1093) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_40,c_12754])).

tff(c_12769,plain,
    ( r2_hidden('#skF_3','#skF_6')
    | ~ r2_hidden('#skF_4','#skF_6')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_11583,c_12761])).

tff(c_12780,plain,(
    r2_hidden('#skF_3','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_38,c_12769])).

tff(c_12782,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_12780])).

tff(c_12783,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_10593])).

tff(c_12797,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10590,c_12783])).

tff(c_12809,plain,(
    r2_hidden('#skF_3','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12797,c_40])).

tff(c_12813,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_12809])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:26:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.53/4.00  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.53/4.02  
% 10.53/4.02  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.53/4.02  %$ r2_orders_2 > m1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 10.53/4.02  
% 10.53/4.02  %Foreground sorts:
% 10.53/4.02  
% 10.53/4.02  
% 10.53/4.02  %Background operators:
% 10.53/4.02  
% 10.53/4.02  
% 10.53/4.02  %Foreground operators:
% 10.53/4.02  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 10.53/4.02  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 10.53/4.02  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 10.53/4.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.53/4.02  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.53/4.02  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.53/4.02  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 10.53/4.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.53/4.02  tff('#skF_5', type, '#skF_5': $i).
% 10.53/4.02  tff('#skF_6', type, '#skF_6': $i).
% 10.53/4.02  tff('#skF_2', type, '#skF_2': $i).
% 10.53/4.02  tff('#skF_3', type, '#skF_3': $i).
% 10.53/4.02  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 10.53/4.02  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 10.53/4.02  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.53/4.02  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 10.53/4.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.53/4.02  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 10.53/4.02  tff('#skF_4', type, '#skF_4': $i).
% 10.53/4.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.53/4.02  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 10.53/4.02  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.53/4.02  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.53/4.02  
% 10.53/4.05  tff(f_196, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(A))) => ((((r2_orders_2(A, B, C) & r2_hidden(B, D)) & r2_hidden(C, E)) & m1_orders_2(E, A, D)) => r2_hidden(B, E)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_orders_2)).
% 10.53/4.05  tff(f_77, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((~(B = k1_xboole_0) => (m1_orders_2(C, A, B) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(A)) & r2_hidden(D, B)) & (C = k3_orders_2(A, B, D)))))) & ((B = k1_xboole_0) => (m1_orders_2(C, A, B) <=> (C = k1_xboole_0)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d15_orders_2)).
% 10.53/4.05  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 10.53/4.05  tff(f_138, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_orders_2)).
% 10.53/4.05  tff(f_162, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_orders_2(A, B, C) => r1_tarski(k3_orders_2(A, D, B), k3_orders_2(A, D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_orders_2)).
% 10.53/4.05  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 10.53/4.05  tff(c_34, plain, (~r2_hidden('#skF_3', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_196])).
% 10.53/4.05  tff(c_48, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_196])).
% 10.53/4.05  tff(c_38, plain, (r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_196])).
% 10.53/4.05  tff(c_60, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_196])).
% 10.53/4.05  tff(c_36, plain, (m1_orders_2('#skF_6', '#skF_2', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_196])).
% 10.53/4.05  tff(c_46, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_196])).
% 10.53/4.05  tff(c_58, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_196])).
% 10.53/4.05  tff(c_56, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_196])).
% 10.53/4.05  tff(c_54, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_196])).
% 10.53/4.05  tff(c_52, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_196])).
% 10.53/4.05  tff(c_44, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_196])).
% 10.53/4.05  tff(c_5962, plain, (![A_521, B_522, C_523]: (r2_hidden('#skF_1'(A_521, B_522, C_523), B_522) | ~m1_orders_2(C_523, A_521, B_522) | k1_xboole_0=B_522 | ~m1_subset_1(C_523, k1_zfmisc_1(u1_struct_0(A_521))) | ~m1_subset_1(B_522, k1_zfmisc_1(u1_struct_0(A_521))) | ~l1_orders_2(A_521) | ~v5_orders_2(A_521) | ~v4_orders_2(A_521) | ~v3_orders_2(A_521) | v2_struct_0(A_521))), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.53/4.05  tff(c_5971, plain, (![B_522]: (r2_hidden('#skF_1'('#skF_2', B_522, '#skF_6'), B_522) | ~m1_orders_2('#skF_6', '#skF_2', B_522) | k1_xboole_0=B_522 | ~m1_subset_1(B_522, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_44, c_5962])).
% 10.53/4.05  tff(c_5982, plain, (![B_522]: (r2_hidden('#skF_1'('#skF_2', B_522, '#skF_6'), B_522) | ~m1_orders_2('#skF_6', '#skF_2', B_522) | k1_xboole_0=B_522 | ~m1_subset_1(B_522, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_5971])).
% 10.53/4.05  tff(c_5988, plain, (![B_524]: (r2_hidden('#skF_1'('#skF_2', B_524, '#skF_6'), B_524) | ~m1_orders_2('#skF_6', '#skF_2', B_524) | k1_xboole_0=B_524 | ~m1_subset_1(B_524, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_5982])).
% 10.53/4.05  tff(c_6000, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_5', '#skF_6'), '#skF_5') | ~m1_orders_2('#skF_6', '#skF_2', '#skF_5') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_46, c_5988])).
% 10.53/4.05  tff(c_6010, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_5', '#skF_6'), '#skF_5') | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_6000])).
% 10.53/4.05  tff(c_6011, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_6010])).
% 10.53/4.05  tff(c_62, plain, (![A_97, B_98]: (r1_tarski(A_97, B_98) | ~m1_subset_1(A_97, k1_zfmisc_1(B_98)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 10.53/4.05  tff(c_74, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_46, c_62])).
% 10.53/4.05  tff(c_370, plain, (![A_170, B_171, C_172]: (r2_hidden('#skF_1'(A_170, B_171, C_172), B_171) | ~m1_orders_2(C_172, A_170, B_171) | k1_xboole_0=B_171 | ~m1_subset_1(C_172, k1_zfmisc_1(u1_struct_0(A_170))) | ~m1_subset_1(B_171, k1_zfmisc_1(u1_struct_0(A_170))) | ~l1_orders_2(A_170) | ~v5_orders_2(A_170) | ~v4_orders_2(A_170) | ~v3_orders_2(A_170) | v2_struct_0(A_170))), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.53/4.05  tff(c_377, plain, (![B_171]: (r2_hidden('#skF_1'('#skF_2', B_171, '#skF_6'), B_171) | ~m1_orders_2('#skF_6', '#skF_2', B_171) | k1_xboole_0=B_171 | ~m1_subset_1(B_171, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_44, c_370])).
% 10.53/4.05  tff(c_384, plain, (![B_171]: (r2_hidden('#skF_1'('#skF_2', B_171, '#skF_6'), B_171) | ~m1_orders_2('#skF_6', '#skF_2', B_171) | k1_xboole_0=B_171 | ~m1_subset_1(B_171, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_377])).
% 10.53/4.05  tff(c_390, plain, (![B_173]: (r2_hidden('#skF_1'('#skF_2', B_173, '#skF_6'), B_173) | ~m1_orders_2('#skF_6', '#skF_2', B_173) | k1_xboole_0=B_173 | ~m1_subset_1(B_173, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_384])).
% 10.53/4.05  tff(c_400, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_5', '#skF_6'), '#skF_5') | ~m1_orders_2('#skF_6', '#skF_2', '#skF_5') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_46, c_390])).
% 10.53/4.05  tff(c_409, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_5', '#skF_6'), '#skF_5') | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_400])).
% 10.53/4.05  tff(c_410, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_409])).
% 10.53/4.05  tff(c_6, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 10.53/4.05  tff(c_248, plain, (![C_139, A_140]: (k1_xboole_0=C_139 | ~m1_orders_2(C_139, A_140, k1_xboole_0) | ~m1_subset_1(C_139, k1_zfmisc_1(u1_struct_0(A_140))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_140))) | ~l1_orders_2(A_140) | ~v5_orders_2(A_140) | ~v4_orders_2(A_140) | ~v3_orders_2(A_140) | v2_struct_0(A_140))), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.53/4.05  tff(c_253, plain, (k1_xboole_0='#skF_6' | ~m1_orders_2('#skF_6', '#skF_2', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_248])).
% 10.53/4.05  tff(c_259, plain, (k1_xboole_0='#skF_6' | ~m1_orders_2('#skF_6', '#skF_2', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_253])).
% 10.53/4.05  tff(c_260, plain, (k1_xboole_0='#skF_6' | ~m1_orders_2('#skF_6', '#skF_2', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_60, c_259])).
% 10.53/4.05  tff(c_265, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_260])).
% 10.53/4.05  tff(c_270, plain, (~r1_tarski(k1_xboole_0, u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_6, c_265])).
% 10.53/4.05  tff(c_415, plain, (~r1_tarski('#skF_5', u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_410, c_270])).
% 10.53/4.05  tff(c_422, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_415])).
% 10.53/4.05  tff(c_424, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_409])).
% 10.53/4.05  tff(c_20, plain, (![A_10, B_22, C_28]: (m1_subset_1('#skF_1'(A_10, B_22, C_28), u1_struct_0(A_10)) | ~m1_orders_2(C_28, A_10, B_22) | k1_xboole_0=B_22 | ~m1_subset_1(C_28, k1_zfmisc_1(u1_struct_0(A_10))) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_10))) | ~l1_orders_2(A_10) | ~v5_orders_2(A_10) | ~v4_orders_2(A_10) | ~v3_orders_2(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.53/4.05  tff(c_686, plain, (![A_206, B_207, C_208]: (k3_orders_2(A_206, B_207, '#skF_1'(A_206, B_207, C_208))=C_208 | ~m1_orders_2(C_208, A_206, B_207) | k1_xboole_0=B_207 | ~m1_subset_1(C_208, k1_zfmisc_1(u1_struct_0(A_206))) | ~m1_subset_1(B_207, k1_zfmisc_1(u1_struct_0(A_206))) | ~l1_orders_2(A_206) | ~v5_orders_2(A_206) | ~v4_orders_2(A_206) | ~v3_orders_2(A_206) | v2_struct_0(A_206))), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.53/4.05  tff(c_696, plain, (![B_207]: (k3_orders_2('#skF_2', B_207, '#skF_1'('#skF_2', B_207, '#skF_6'))='#skF_6' | ~m1_orders_2('#skF_6', '#skF_2', B_207) | k1_xboole_0=B_207 | ~m1_subset_1(B_207, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_44, c_686])).
% 10.53/4.05  tff(c_704, plain, (![B_207]: (k3_orders_2('#skF_2', B_207, '#skF_1'('#skF_2', B_207, '#skF_6'))='#skF_6' | ~m1_orders_2('#skF_6', '#skF_2', B_207) | k1_xboole_0=B_207 | ~m1_subset_1(B_207, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_696])).
% 10.53/4.05  tff(c_711, plain, (![B_209]: (k3_orders_2('#skF_2', B_209, '#skF_1'('#skF_2', B_209, '#skF_6'))='#skF_6' | ~m1_orders_2('#skF_6', '#skF_2', B_209) | k1_xboole_0=B_209 | ~m1_subset_1(B_209, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_704])).
% 10.53/4.05  tff(c_724, plain, (k3_orders_2('#skF_2', '#skF_5', '#skF_1'('#skF_2', '#skF_5', '#skF_6'))='#skF_6' | ~m1_orders_2('#skF_6', '#skF_2', '#skF_5') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_46, c_711])).
% 10.53/4.05  tff(c_734, plain, (k3_orders_2('#skF_2', '#skF_5', '#skF_1'('#skF_2', '#skF_5', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_724])).
% 10.53/4.05  tff(c_735, plain, (k3_orders_2('#skF_2', '#skF_5', '#skF_1'('#skF_2', '#skF_5', '#skF_6'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_424, c_734])).
% 10.53/4.05  tff(c_28, plain, (![B_47, D_53, A_39, C_51]: (r2_hidden(B_47, D_53) | ~r2_hidden(B_47, k3_orders_2(A_39, D_53, C_51)) | ~m1_subset_1(D_53, k1_zfmisc_1(u1_struct_0(A_39))) | ~m1_subset_1(C_51, u1_struct_0(A_39)) | ~m1_subset_1(B_47, u1_struct_0(A_39)) | ~l1_orders_2(A_39) | ~v5_orders_2(A_39) | ~v4_orders_2(A_39) | ~v3_orders_2(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_138])).
% 10.53/4.05  tff(c_749, plain, (![B_47]: (r2_hidden(B_47, '#skF_5') | ~r2_hidden(B_47, '#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_47, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_735, c_28])).
% 10.53/4.05  tff(c_776, plain, (![B_47]: (r2_hidden(B_47, '#skF_5') | ~r2_hidden(B_47, '#skF_6') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_47, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_46, c_749])).
% 10.53/4.05  tff(c_777, plain, (![B_47]: (r2_hidden(B_47, '#skF_5') | ~r2_hidden(B_47, '#skF_6') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_47, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_60, c_776])).
% 10.53/4.05  tff(c_885, plain, (~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_777])).
% 10.53/4.05  tff(c_888, plain, (~m1_orders_2('#skF_6', '#skF_2', '#skF_5') | k1_xboole_0='#skF_5' | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_20, c_885])).
% 10.53/4.05  tff(c_900, plain, (k1_xboole_0='#skF_5' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_46, c_44, c_36, c_888])).
% 10.53/4.05  tff(c_902, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_424, c_900])).
% 10.53/4.05  tff(c_904, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_777])).
% 10.53/4.05  tff(c_30, plain, (![A_39, B_47, C_51, D_53]: (r2_orders_2(A_39, B_47, C_51) | ~r2_hidden(B_47, k3_orders_2(A_39, D_53, C_51)) | ~m1_subset_1(D_53, k1_zfmisc_1(u1_struct_0(A_39))) | ~m1_subset_1(C_51, u1_struct_0(A_39)) | ~m1_subset_1(B_47, u1_struct_0(A_39)) | ~l1_orders_2(A_39) | ~v5_orders_2(A_39) | ~v4_orders_2(A_39) | ~v3_orders_2(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_138])).
% 10.53/4.05  tff(c_741, plain, (![B_47]: (r2_orders_2('#skF_2', B_47, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~r2_hidden(B_47, '#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_47, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_735, c_30])).
% 10.53/4.05  tff(c_769, plain, (![B_47]: (r2_orders_2('#skF_2', B_47, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~r2_hidden(B_47, '#skF_6') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_47, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_46, c_741])).
% 10.53/4.05  tff(c_770, plain, (![B_47]: (r2_orders_2('#skF_2', B_47, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~r2_hidden(B_47, '#skF_6') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_47, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_60, c_769])).
% 10.53/4.05  tff(c_1417, plain, (![B_269]: (r2_orders_2('#skF_2', B_269, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~r2_hidden(B_269, '#skF_6') | ~m1_subset_1(B_269, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_904, c_770])).
% 10.53/4.05  tff(c_1002, plain, (![A_225, D_226, B_227, C_228]: (r1_tarski(k3_orders_2(A_225, D_226, B_227), k3_orders_2(A_225, D_226, C_228)) | ~r2_orders_2(A_225, B_227, C_228) | ~m1_subset_1(D_226, k1_zfmisc_1(u1_struct_0(A_225))) | ~m1_subset_1(C_228, u1_struct_0(A_225)) | ~m1_subset_1(B_227, u1_struct_0(A_225)) | ~l1_orders_2(A_225) | ~v5_orders_2(A_225) | ~v4_orders_2(A_225) | ~v3_orders_2(A_225) | v2_struct_0(A_225))), inference(cnfTransformation, [status(thm)], [f_162])).
% 10.53/4.05  tff(c_1018, plain, (![B_227]: (r1_tarski(k3_orders_2('#skF_2', '#skF_5', B_227), '#skF_6') | ~r2_orders_2('#skF_2', B_227, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_227, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_735, c_1002])).
% 10.53/4.05  tff(c_1028, plain, (![B_227]: (r1_tarski(k3_orders_2('#skF_2', '#skF_5', B_227), '#skF_6') | ~r2_orders_2('#skF_2', B_227, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~m1_subset_1(B_227, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_904, c_46, c_1018])).
% 10.53/4.05  tff(c_1029, plain, (![B_227]: (r1_tarski(k3_orders_2('#skF_2', '#skF_5', B_227), '#skF_6') | ~r2_orders_2('#skF_2', B_227, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~m1_subset_1(B_227, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_60, c_1028])).
% 10.53/4.05  tff(c_1429, plain, (![B_269]: (r1_tarski(k3_orders_2('#skF_2', '#skF_5', B_269), '#skF_6') | ~r2_hidden(B_269, '#skF_6') | ~m1_subset_1(B_269, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_1417, c_1029])).
% 10.53/4.05  tff(c_50, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_196])).
% 10.53/4.05  tff(c_40, plain, (r2_hidden('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_196])).
% 10.53/4.05  tff(c_42, plain, (r2_orders_2('#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_196])).
% 10.53/4.05  tff(c_861, plain, (![B_216, A_217, D_218, C_219]: (r2_hidden(B_216, k3_orders_2(A_217, D_218, C_219)) | ~r2_hidden(B_216, D_218) | ~r2_orders_2(A_217, B_216, C_219) | ~m1_subset_1(D_218, k1_zfmisc_1(u1_struct_0(A_217))) | ~m1_subset_1(C_219, u1_struct_0(A_217)) | ~m1_subset_1(B_216, u1_struct_0(A_217)) | ~l1_orders_2(A_217) | ~v5_orders_2(A_217) | ~v4_orders_2(A_217) | ~v3_orders_2(A_217) | v2_struct_0(A_217))), inference(cnfTransformation, [status(thm)], [f_138])).
% 10.53/4.05  tff(c_873, plain, (![B_216, C_219]: (r2_hidden(B_216, k3_orders_2('#skF_2', '#skF_5', C_219)) | ~r2_hidden(B_216, '#skF_5') | ~r2_orders_2('#skF_2', B_216, C_219) | ~m1_subset_1(C_219, u1_struct_0('#skF_2')) | ~m1_subset_1(B_216, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_46, c_861])).
% 10.53/4.05  tff(c_883, plain, (![B_216, C_219]: (r2_hidden(B_216, k3_orders_2('#skF_2', '#skF_5', C_219)) | ~r2_hidden(B_216, '#skF_5') | ~r2_orders_2('#skF_2', B_216, C_219) | ~m1_subset_1(C_219, u1_struct_0('#skF_2')) | ~m1_subset_1(B_216, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_873])).
% 10.53/4.05  tff(c_1242, plain, (![B_256, C_257]: (r2_hidden(B_256, k3_orders_2('#skF_2', '#skF_5', C_257)) | ~r2_hidden(B_256, '#skF_5') | ~r2_orders_2('#skF_2', B_256, C_257) | ~m1_subset_1(C_257, u1_struct_0('#skF_2')) | ~m1_subset_1(B_256, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_60, c_883])).
% 10.53/4.05  tff(c_2, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.53/4.05  tff(c_4220, plain, (![B_438, A_439, C_440]: (r2_hidden(B_438, A_439) | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', C_440), k1_zfmisc_1(A_439)) | ~r2_hidden(B_438, '#skF_5') | ~r2_orders_2('#skF_2', B_438, C_440) | ~m1_subset_1(C_440, u1_struct_0('#skF_2')) | ~m1_subset_1(B_438, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_1242, c_2])).
% 10.53/4.05  tff(c_5794, plain, (![B_508, B_509, C_510]: (r2_hidden(B_508, B_509) | ~r2_hidden(B_508, '#skF_5') | ~r2_orders_2('#skF_2', B_508, C_510) | ~m1_subset_1(C_510, u1_struct_0('#skF_2')) | ~m1_subset_1(B_508, u1_struct_0('#skF_2')) | ~r1_tarski(k3_orders_2('#skF_2', '#skF_5', C_510), B_509))), inference(resolution, [status(thm)], [c_6, c_4220])).
% 10.53/4.05  tff(c_5798, plain, (![B_509]: (r2_hidden('#skF_3', B_509) | ~r2_hidden('#skF_3', '#skF_5') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~r1_tarski(k3_orders_2('#skF_2', '#skF_5', '#skF_4'), B_509))), inference(resolution, [status(thm)], [c_42, c_5794])).
% 10.53/4.05  tff(c_5805, plain, (![B_511]: (r2_hidden('#skF_3', B_511) | ~r1_tarski(k3_orders_2('#skF_2', '#skF_5', '#skF_4'), B_511))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_40, c_5798])).
% 10.53/4.05  tff(c_5817, plain, (r2_hidden('#skF_3', '#skF_6') | ~r2_hidden('#skF_4', '#skF_6') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_1429, c_5805])).
% 10.53/4.05  tff(c_5834, plain, (r2_hidden('#skF_3', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_38, c_5817])).
% 10.53/4.05  tff(c_5836, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_5834])).
% 10.53/4.05  tff(c_5837, plain, (~m1_orders_2('#skF_6', '#skF_2', k1_xboole_0) | k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_260])).
% 10.53/4.05  tff(c_5910, plain, (~m1_orders_2('#skF_6', '#skF_2', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_5837])).
% 10.53/4.05  tff(c_6019, plain, (~m1_orders_2('#skF_6', '#skF_2', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6011, c_5910])).
% 10.53/4.05  tff(c_6028, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_6019])).
% 10.53/4.05  tff(c_6030, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_6010])).
% 10.53/4.05  tff(c_6224, plain, (![A_545, B_546, C_547]: (k3_orders_2(A_545, B_546, '#skF_1'(A_545, B_546, C_547))=C_547 | ~m1_orders_2(C_547, A_545, B_546) | k1_xboole_0=B_546 | ~m1_subset_1(C_547, k1_zfmisc_1(u1_struct_0(A_545))) | ~m1_subset_1(B_546, k1_zfmisc_1(u1_struct_0(A_545))) | ~l1_orders_2(A_545) | ~v5_orders_2(A_545) | ~v4_orders_2(A_545) | ~v3_orders_2(A_545) | v2_struct_0(A_545))), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.53/4.05  tff(c_6236, plain, (![B_546]: (k3_orders_2('#skF_2', B_546, '#skF_1'('#skF_2', B_546, '#skF_6'))='#skF_6' | ~m1_orders_2('#skF_6', '#skF_2', B_546) | k1_xboole_0=B_546 | ~m1_subset_1(B_546, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_44, c_6224])).
% 10.53/4.05  tff(c_6248, plain, (![B_546]: (k3_orders_2('#skF_2', B_546, '#skF_1'('#skF_2', B_546, '#skF_6'))='#skF_6' | ~m1_orders_2('#skF_6', '#skF_2', B_546) | k1_xboole_0=B_546 | ~m1_subset_1(B_546, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_6236])).
% 10.53/4.05  tff(c_6301, plain, (![B_553]: (k3_orders_2('#skF_2', B_553, '#skF_1'('#skF_2', B_553, '#skF_6'))='#skF_6' | ~m1_orders_2('#skF_6', '#skF_2', B_553) | k1_xboole_0=B_553 | ~m1_subset_1(B_553, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_6248])).
% 10.53/4.05  tff(c_6316, plain, (k3_orders_2('#skF_2', '#skF_5', '#skF_1'('#skF_2', '#skF_5', '#skF_6'))='#skF_6' | ~m1_orders_2('#skF_6', '#skF_2', '#skF_5') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_46, c_6301])).
% 10.53/4.05  tff(c_6327, plain, (k3_orders_2('#skF_2', '#skF_5', '#skF_1'('#skF_2', '#skF_5', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_6316])).
% 10.53/4.05  tff(c_6328, plain, (k3_orders_2('#skF_2', '#skF_5', '#skF_1'('#skF_2', '#skF_5', '#skF_6'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_6030, c_6327])).
% 10.53/4.05  tff(c_6333, plain, (![B_47]: (r2_hidden(B_47, '#skF_5') | ~r2_hidden(B_47, '#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_47, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_6328, c_28])).
% 10.53/4.05  tff(c_6343, plain, (![B_47]: (r2_hidden(B_47, '#skF_5') | ~r2_hidden(B_47, '#skF_6') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_47, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_46, c_6333])).
% 10.53/4.05  tff(c_6344, plain, (![B_47]: (r2_hidden(B_47, '#skF_5') | ~r2_hidden(B_47, '#skF_6') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_47, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_60, c_6343])).
% 10.53/4.05  tff(c_6406, plain, (~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_6344])).
% 10.53/4.05  tff(c_6409, plain, (~m1_orders_2('#skF_6', '#skF_2', '#skF_5') | k1_xboole_0='#skF_5' | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_20, c_6406])).
% 10.53/4.05  tff(c_6424, plain, (k1_xboole_0='#skF_5' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_46, c_44, c_36, c_6409])).
% 10.53/4.05  tff(c_6426, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_6030, c_6424])).
% 10.53/4.05  tff(c_6428, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_6344])).
% 10.53/4.05  tff(c_6331, plain, (![B_47]: (r2_orders_2('#skF_2', B_47, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~r2_hidden(B_47, '#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_47, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_6328, c_30])).
% 10.53/4.05  tff(c_6340, plain, (![B_47]: (r2_orders_2('#skF_2', B_47, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~r2_hidden(B_47, '#skF_6') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_47, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_46, c_6331])).
% 10.53/4.05  tff(c_6341, plain, (![B_47]: (r2_orders_2('#skF_2', B_47, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~r2_hidden(B_47, '#skF_6') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_47, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_60, c_6340])).
% 10.53/4.05  tff(c_7317, plain, (![B_47]: (r2_orders_2('#skF_2', B_47, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~r2_hidden(B_47, '#skF_6') | ~m1_subset_1(B_47, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_6428, c_6341])).
% 10.53/4.05  tff(c_6376, plain, (![A_558, D_559, B_560, C_561]: (r1_tarski(k3_orders_2(A_558, D_559, B_560), k3_orders_2(A_558, D_559, C_561)) | ~r2_orders_2(A_558, B_560, C_561) | ~m1_subset_1(D_559, k1_zfmisc_1(u1_struct_0(A_558))) | ~m1_subset_1(C_561, u1_struct_0(A_558)) | ~m1_subset_1(B_560, u1_struct_0(A_558)) | ~l1_orders_2(A_558) | ~v5_orders_2(A_558) | ~v4_orders_2(A_558) | ~v3_orders_2(A_558) | v2_struct_0(A_558))), inference(cnfTransformation, [status(thm)], [f_162])).
% 10.53/4.05  tff(c_6392, plain, (![B_560]: (r1_tarski(k3_orders_2('#skF_2', '#skF_5', B_560), '#skF_6') | ~r2_orders_2('#skF_2', B_560, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_560, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_6328, c_6376])).
% 10.53/4.05  tff(c_6402, plain, (![B_560]: (r1_tarski(k3_orders_2('#skF_2', '#skF_5', B_560), '#skF_6') | ~r2_orders_2('#skF_2', B_560, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_560, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_46, c_6392])).
% 10.53/4.05  tff(c_6403, plain, (![B_560]: (r1_tarski(k3_orders_2('#skF_2', '#skF_5', B_560), '#skF_6') | ~r2_orders_2('#skF_2', B_560, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_560, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_60, c_6402])).
% 10.53/4.05  tff(c_8311, plain, (![B_687]: (r1_tarski(k3_orders_2('#skF_2', '#skF_5', B_687), '#skF_6') | ~r2_orders_2('#skF_2', B_687, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~m1_subset_1(B_687, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_6428, c_6403])).
% 10.53/4.05  tff(c_8315, plain, (![B_47]: (r1_tarski(k3_orders_2('#skF_2', '#skF_5', B_47), '#skF_6') | ~r2_hidden(B_47, '#skF_6') | ~m1_subset_1(B_47, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_7317, c_8311])).
% 10.53/4.05  tff(c_6473, plain, (![B_563, A_564, D_565, C_566]: (r2_hidden(B_563, k3_orders_2(A_564, D_565, C_566)) | ~r2_hidden(B_563, D_565) | ~r2_orders_2(A_564, B_563, C_566) | ~m1_subset_1(D_565, k1_zfmisc_1(u1_struct_0(A_564))) | ~m1_subset_1(C_566, u1_struct_0(A_564)) | ~m1_subset_1(B_563, u1_struct_0(A_564)) | ~l1_orders_2(A_564) | ~v5_orders_2(A_564) | ~v4_orders_2(A_564) | ~v3_orders_2(A_564) | v2_struct_0(A_564))), inference(cnfTransformation, [status(thm)], [f_138])).
% 10.53/4.05  tff(c_6487, plain, (![B_563, C_566]: (r2_hidden(B_563, k3_orders_2('#skF_2', '#skF_5', C_566)) | ~r2_hidden(B_563, '#skF_5') | ~r2_orders_2('#skF_2', B_563, C_566) | ~m1_subset_1(C_566, u1_struct_0('#skF_2')) | ~m1_subset_1(B_563, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_46, c_6473])).
% 10.53/4.05  tff(c_6501, plain, (![B_563, C_566]: (r2_hidden(B_563, k3_orders_2('#skF_2', '#skF_5', C_566)) | ~r2_hidden(B_563, '#skF_5') | ~r2_orders_2('#skF_2', B_563, C_566) | ~m1_subset_1(C_566, u1_struct_0('#skF_2')) | ~m1_subset_1(B_563, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_6487])).
% 10.53/4.05  tff(c_6816, plain, (![B_602, C_603]: (r2_hidden(B_602, k3_orders_2('#skF_2', '#skF_5', C_603)) | ~r2_hidden(B_602, '#skF_5') | ~r2_orders_2('#skF_2', B_602, C_603) | ~m1_subset_1(C_603, u1_struct_0('#skF_2')) | ~m1_subset_1(B_602, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_60, c_6501])).
% 10.53/4.05  tff(c_9269, plain, (![B_786, A_787, C_788]: (r2_hidden(B_786, A_787) | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', C_788), k1_zfmisc_1(A_787)) | ~r2_hidden(B_786, '#skF_5') | ~r2_orders_2('#skF_2', B_786, C_788) | ~m1_subset_1(C_788, u1_struct_0('#skF_2')) | ~m1_subset_1(B_786, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_6816, c_2])).
% 10.53/4.05  tff(c_10557, plain, (![B_857, B_858, C_859]: (r2_hidden(B_857, B_858) | ~r2_hidden(B_857, '#skF_5') | ~r2_orders_2('#skF_2', B_857, C_859) | ~m1_subset_1(C_859, u1_struct_0('#skF_2')) | ~m1_subset_1(B_857, u1_struct_0('#skF_2')) | ~r1_tarski(k3_orders_2('#skF_2', '#skF_5', C_859), B_858))), inference(resolution, [status(thm)], [c_6, c_9269])).
% 10.53/4.05  tff(c_10561, plain, (![B_858]: (r2_hidden('#skF_3', B_858) | ~r2_hidden('#skF_3', '#skF_5') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~r1_tarski(k3_orders_2('#skF_2', '#skF_5', '#skF_4'), B_858))), inference(resolution, [status(thm)], [c_42, c_10557])).
% 10.53/4.05  tff(c_10568, plain, (![B_860]: (r2_hidden('#skF_3', B_860) | ~r1_tarski(k3_orders_2('#skF_2', '#skF_5', '#skF_4'), B_860))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_40, c_10561])).
% 10.53/4.05  tff(c_10572, plain, (r2_hidden('#skF_3', '#skF_6') | ~r2_hidden('#skF_4', '#skF_6') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_8315, c_10568])).
% 10.53/4.05  tff(c_10587, plain, (r2_hidden('#skF_3', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_38, c_10572])).
% 10.53/4.05  tff(c_10589, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_10587])).
% 10.53/4.05  tff(c_10590, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_5837])).
% 10.53/4.05  tff(c_10591, plain, (m1_orders_2('#skF_6', '#skF_2', k1_xboole_0)), inference(splitRight, [status(thm)], [c_5837])).
% 10.53/4.05  tff(c_10607, plain, (m1_orders_2('#skF_6', '#skF_2', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_10590, c_10591])).
% 10.53/4.05  tff(c_18, plain, (![A_10, B_22, C_28]: (r2_hidden('#skF_1'(A_10, B_22, C_28), B_22) | ~m1_orders_2(C_28, A_10, B_22) | k1_xboole_0=B_22 | ~m1_subset_1(C_28, k1_zfmisc_1(u1_struct_0(A_10))) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_10))) | ~l1_orders_2(A_10) | ~v5_orders_2(A_10) | ~v4_orders_2(A_10) | ~v3_orders_2(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.53/4.05  tff(c_10618, plain, (![A_861, B_862, C_863]: (r2_hidden('#skF_1'(A_861, B_862, C_863), B_862) | ~m1_orders_2(C_863, A_861, B_862) | B_862='#skF_6' | ~m1_subset_1(C_863, k1_zfmisc_1(u1_struct_0(A_861))) | ~m1_subset_1(B_862, k1_zfmisc_1(u1_struct_0(A_861))) | ~l1_orders_2(A_861) | ~v5_orders_2(A_861) | ~v4_orders_2(A_861) | ~v3_orders_2(A_861) | v2_struct_0(A_861))), inference(demodulation, [status(thm), theory('equality')], [c_10590, c_18])).
% 10.53/4.05  tff(c_10625, plain, (![B_862]: (r2_hidden('#skF_1'('#skF_2', B_862, '#skF_6'), B_862) | ~m1_orders_2('#skF_6', '#skF_2', B_862) | B_862='#skF_6' | ~m1_subset_1(B_862, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_44, c_10618])).
% 10.53/4.05  tff(c_10632, plain, (![B_862]: (r2_hidden('#skF_1'('#skF_2', B_862, '#skF_6'), B_862) | ~m1_orders_2('#skF_6', '#skF_2', B_862) | B_862='#skF_6' | ~m1_subset_1(B_862, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_10625])).
% 10.53/4.05  tff(c_10638, plain, (![B_864]: (r2_hidden('#skF_1'('#skF_2', B_864, '#skF_6'), B_864) | ~m1_orders_2('#skF_6', '#skF_2', B_864) | B_864='#skF_6' | ~m1_subset_1(B_864, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_10632])).
% 10.53/4.05  tff(c_10648, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_5', '#skF_6'), '#skF_5') | ~m1_orders_2('#skF_6', '#skF_2', '#skF_5') | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_46, c_10638])).
% 10.53/4.05  tff(c_10660, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_5', '#skF_6'), '#skF_5') | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_10648])).
% 10.53/4.05  tff(c_10661, plain, ('#skF_5'='#skF_6'), inference(splitLeft, [status(thm)], [c_10660])).
% 10.53/4.05  tff(c_5838, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_260])).
% 10.53/4.05  tff(c_255, plain, (k1_xboole_0='#skF_5' | ~m1_orders_2('#skF_5', '#skF_2', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_46, c_248])).
% 10.53/4.05  tff(c_263, plain, (k1_xboole_0='#skF_5' | ~m1_orders_2('#skF_5', '#skF_2', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_255])).
% 10.53/4.05  tff(c_264, plain, (k1_xboole_0='#skF_5' | ~m1_orders_2('#skF_5', '#skF_2', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_60, c_263])).
% 10.53/4.05  tff(c_10593, plain, (k1_xboole_0='#skF_5' | ~m1_orders_2('#skF_5', '#skF_2', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_5838, c_264])).
% 10.53/4.05  tff(c_10594, plain, (~m1_orders_2('#skF_5', '#skF_2', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_10593])).
% 10.53/4.05  tff(c_10614, plain, (~m1_orders_2('#skF_5', '#skF_2', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_10590, c_10594])).
% 10.53/4.05  tff(c_10662, plain, (~m1_orders_2('#skF_6', '#skF_2', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_10661, c_10614])).
% 10.53/4.05  tff(c_10677, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10607, c_10662])).
% 10.53/4.05  tff(c_10679, plain, ('#skF_5'!='#skF_6'), inference(splitRight, [status(thm)], [c_10660])).
% 10.53/4.05  tff(c_10851, plain, (![A_10, B_22, C_28]: (m1_subset_1('#skF_1'(A_10, B_22, C_28), u1_struct_0(A_10)) | ~m1_orders_2(C_28, A_10, B_22) | B_22='#skF_6' | ~m1_subset_1(C_28, k1_zfmisc_1(u1_struct_0(A_10))) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_10))) | ~l1_orders_2(A_10) | ~v5_orders_2(A_10) | ~v4_orders_2(A_10) | ~v3_orders_2(A_10) | v2_struct_0(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_10590, c_20])).
% 10.53/4.05  tff(c_16, plain, (![A_10, B_22, C_28]: (k3_orders_2(A_10, B_22, '#skF_1'(A_10, B_22, C_28))=C_28 | ~m1_orders_2(C_28, A_10, B_22) | k1_xboole_0=B_22 | ~m1_subset_1(C_28, k1_zfmisc_1(u1_struct_0(A_10))) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_10))) | ~l1_orders_2(A_10) | ~v5_orders_2(A_10) | ~v4_orders_2(A_10) | ~v3_orders_2(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.53/4.05  tff(c_10920, plain, (![A_897, B_898, C_899]: (k3_orders_2(A_897, B_898, '#skF_1'(A_897, B_898, C_899))=C_899 | ~m1_orders_2(C_899, A_897, B_898) | B_898='#skF_6' | ~m1_subset_1(C_899, k1_zfmisc_1(u1_struct_0(A_897))) | ~m1_subset_1(B_898, k1_zfmisc_1(u1_struct_0(A_897))) | ~l1_orders_2(A_897) | ~v5_orders_2(A_897) | ~v4_orders_2(A_897) | ~v3_orders_2(A_897) | v2_struct_0(A_897))), inference(demodulation, [status(thm), theory('equality')], [c_10590, c_16])).
% 10.53/4.05  tff(c_10930, plain, (![B_898]: (k3_orders_2('#skF_2', B_898, '#skF_1'('#skF_2', B_898, '#skF_6'))='#skF_6' | ~m1_orders_2('#skF_6', '#skF_2', B_898) | B_898='#skF_6' | ~m1_subset_1(B_898, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_44, c_10920])).
% 10.53/4.05  tff(c_10938, plain, (![B_898]: (k3_orders_2('#skF_2', B_898, '#skF_1'('#skF_2', B_898, '#skF_6'))='#skF_6' | ~m1_orders_2('#skF_6', '#skF_2', B_898) | B_898='#skF_6' | ~m1_subset_1(B_898, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_10930])).
% 10.53/4.05  tff(c_10962, plain, (![B_904]: (k3_orders_2('#skF_2', B_904, '#skF_1'('#skF_2', B_904, '#skF_6'))='#skF_6' | ~m1_orders_2('#skF_6', '#skF_2', B_904) | B_904='#skF_6' | ~m1_subset_1(B_904, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_10938])).
% 10.53/4.05  tff(c_10975, plain, (k3_orders_2('#skF_2', '#skF_5', '#skF_1'('#skF_2', '#skF_5', '#skF_6'))='#skF_6' | ~m1_orders_2('#skF_6', '#skF_2', '#skF_5') | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_46, c_10962])).
% 10.53/4.05  tff(c_10988, plain, (k3_orders_2('#skF_2', '#skF_5', '#skF_1'('#skF_2', '#skF_5', '#skF_6'))='#skF_6' | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_10975])).
% 10.53/4.05  tff(c_10989, plain, (k3_orders_2('#skF_2', '#skF_5', '#skF_1'('#skF_2', '#skF_5', '#skF_6'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_10679, c_10988])).
% 10.53/4.05  tff(c_11006, plain, (![B_47]: (r2_hidden(B_47, '#skF_5') | ~r2_hidden(B_47, '#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_47, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_10989, c_28])).
% 10.53/4.05  tff(c_11024, plain, (![B_47]: (r2_hidden(B_47, '#skF_5') | ~r2_hidden(B_47, '#skF_6') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_47, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_46, c_11006])).
% 10.53/4.05  tff(c_11025, plain, (![B_47]: (r2_hidden(B_47, '#skF_5') | ~r2_hidden(B_47, '#skF_6') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_47, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_60, c_11024])).
% 10.53/4.05  tff(c_11068, plain, (~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_11025])).
% 10.53/4.05  tff(c_11071, plain, (~m1_orders_2('#skF_6', '#skF_2', '#skF_5') | '#skF_5'='#skF_6' | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_10851, c_11068])).
% 10.53/4.05  tff(c_11083, plain, ('#skF_5'='#skF_6' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_46, c_44, c_36, c_11071])).
% 10.53/4.05  tff(c_11085, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_10679, c_11083])).
% 10.53/4.05  tff(c_11087, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_11025])).
% 10.53/4.05  tff(c_10998, plain, (![B_47]: (r2_orders_2('#skF_2', B_47, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~r2_hidden(B_47, '#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_47, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_10989, c_30])).
% 10.53/4.05  tff(c_11017, plain, (![B_47]: (r2_orders_2('#skF_2', B_47, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~r2_hidden(B_47, '#skF_6') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_47, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_46, c_10998])).
% 10.53/4.05  tff(c_11018, plain, (![B_47]: (r2_orders_2('#skF_2', B_47, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~r2_hidden(B_47, '#skF_6') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_47, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_60, c_11017])).
% 10.53/4.05  tff(c_11571, plain, (![B_961]: (r2_orders_2('#skF_2', B_961, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~r2_hidden(B_961, '#skF_6') | ~m1_subset_1(B_961, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_11087, c_11018])).
% 10.53/4.05  tff(c_11228, plain, (![A_919, D_920, B_921, C_922]: (r1_tarski(k3_orders_2(A_919, D_920, B_921), k3_orders_2(A_919, D_920, C_922)) | ~r2_orders_2(A_919, B_921, C_922) | ~m1_subset_1(D_920, k1_zfmisc_1(u1_struct_0(A_919))) | ~m1_subset_1(C_922, u1_struct_0(A_919)) | ~m1_subset_1(B_921, u1_struct_0(A_919)) | ~l1_orders_2(A_919) | ~v5_orders_2(A_919) | ~v4_orders_2(A_919) | ~v3_orders_2(A_919) | v2_struct_0(A_919))), inference(cnfTransformation, [status(thm)], [f_162])).
% 10.53/4.05  tff(c_11244, plain, (![B_921]: (r1_tarski(k3_orders_2('#skF_2', '#skF_5', B_921), '#skF_6') | ~r2_orders_2('#skF_2', B_921, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_921, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_10989, c_11228])).
% 10.53/4.05  tff(c_11254, plain, (![B_921]: (r1_tarski(k3_orders_2('#skF_2', '#skF_5', B_921), '#skF_6') | ~r2_orders_2('#skF_2', B_921, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~m1_subset_1(B_921, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_11087, c_46, c_11244])).
% 10.53/4.05  tff(c_11255, plain, (![B_921]: (r1_tarski(k3_orders_2('#skF_2', '#skF_5', B_921), '#skF_6') | ~r2_orders_2('#skF_2', B_921, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~m1_subset_1(B_921, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_60, c_11254])).
% 10.53/4.05  tff(c_11583, plain, (![B_961]: (r1_tarski(k3_orders_2('#skF_2', '#skF_5', B_961), '#skF_6') | ~r2_hidden(B_961, '#skF_6') | ~m1_subset_1(B_961, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_11571, c_11255])).
% 10.53/4.05  tff(c_11088, plain, (![B_907, A_908, D_909, C_910]: (r2_hidden(B_907, k3_orders_2(A_908, D_909, C_910)) | ~r2_hidden(B_907, D_909) | ~r2_orders_2(A_908, B_907, C_910) | ~m1_subset_1(D_909, k1_zfmisc_1(u1_struct_0(A_908))) | ~m1_subset_1(C_910, u1_struct_0(A_908)) | ~m1_subset_1(B_907, u1_struct_0(A_908)) | ~l1_orders_2(A_908) | ~v5_orders_2(A_908) | ~v4_orders_2(A_908) | ~v3_orders_2(A_908) | v2_struct_0(A_908))), inference(cnfTransformation, [status(thm)], [f_138])).
% 10.53/4.05  tff(c_11100, plain, (![B_907, C_910]: (r2_hidden(B_907, k3_orders_2('#skF_2', '#skF_5', C_910)) | ~r2_hidden(B_907, '#skF_5') | ~r2_orders_2('#skF_2', B_907, C_910) | ~m1_subset_1(C_910, u1_struct_0('#skF_2')) | ~m1_subset_1(B_907, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_46, c_11088])).
% 10.53/4.05  tff(c_11110, plain, (![B_907, C_910]: (r2_hidden(B_907, k3_orders_2('#skF_2', '#skF_5', C_910)) | ~r2_hidden(B_907, '#skF_5') | ~r2_orders_2('#skF_2', B_907, C_910) | ~m1_subset_1(C_910, u1_struct_0('#skF_2')) | ~m1_subset_1(B_907, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_11100])).
% 10.53/4.05  tff(c_11460, plain, (![B_949, C_950]: (r2_hidden(B_949, k3_orders_2('#skF_2', '#skF_5', C_950)) | ~r2_hidden(B_949, '#skF_5') | ~r2_orders_2('#skF_2', B_949, C_950) | ~m1_subset_1(C_950, u1_struct_0('#skF_2')) | ~m1_subset_1(B_949, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_60, c_11110])).
% 10.53/4.05  tff(c_12496, plain, (![B_1067, A_1068, C_1069]: (r2_hidden(B_1067, A_1068) | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', C_1069), k1_zfmisc_1(A_1068)) | ~r2_hidden(B_1067, '#skF_5') | ~r2_orders_2('#skF_2', B_1067, C_1069) | ~m1_subset_1(C_1069, u1_struct_0('#skF_2')) | ~m1_subset_1(B_1067, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_11460, c_2])).
% 10.53/4.05  tff(c_12750, plain, (![B_1090, B_1091, C_1092]: (r2_hidden(B_1090, B_1091) | ~r2_hidden(B_1090, '#skF_5') | ~r2_orders_2('#skF_2', B_1090, C_1092) | ~m1_subset_1(C_1092, u1_struct_0('#skF_2')) | ~m1_subset_1(B_1090, u1_struct_0('#skF_2')) | ~r1_tarski(k3_orders_2('#skF_2', '#skF_5', C_1092), B_1091))), inference(resolution, [status(thm)], [c_6, c_12496])).
% 10.53/4.05  tff(c_12754, plain, (![B_1091]: (r2_hidden('#skF_3', B_1091) | ~r2_hidden('#skF_3', '#skF_5') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~r1_tarski(k3_orders_2('#skF_2', '#skF_5', '#skF_4'), B_1091))), inference(resolution, [status(thm)], [c_42, c_12750])).
% 10.53/4.05  tff(c_12761, plain, (![B_1093]: (r2_hidden('#skF_3', B_1093) | ~r1_tarski(k3_orders_2('#skF_2', '#skF_5', '#skF_4'), B_1093))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_40, c_12754])).
% 10.53/4.05  tff(c_12769, plain, (r2_hidden('#skF_3', '#skF_6') | ~r2_hidden('#skF_4', '#skF_6') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_11583, c_12761])).
% 10.53/4.05  tff(c_12780, plain, (r2_hidden('#skF_3', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_38, c_12769])).
% 10.53/4.05  tff(c_12782, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_12780])).
% 10.53/4.05  tff(c_12783, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_10593])).
% 10.53/4.05  tff(c_12797, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_10590, c_12783])).
% 10.53/4.05  tff(c_12809, plain, (r2_hidden('#skF_3', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_12797, c_40])).
% 10.53/4.05  tff(c_12813, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_12809])).
% 10.53/4.05  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.53/4.05  
% 10.53/4.05  Inference rules
% 10.53/4.05  ----------------------
% 10.53/4.05  #Ref     : 0
% 10.53/4.05  #Sup     : 2910
% 10.53/4.05  #Fact    : 0
% 10.53/4.05  #Define  : 0
% 10.53/4.05  #Split   : 85
% 10.53/4.05  #Chain   : 0
% 10.53/4.05  #Close   : 0
% 10.53/4.05  
% 10.53/4.05  Ordering : KBO
% 10.53/4.05  
% 10.53/4.05  Simplification rules
% 10.53/4.05  ----------------------
% 10.53/4.05  #Subsume      : 809
% 10.53/4.05  #Demod        : 2596
% 10.53/4.05  #Tautology    : 290
% 10.53/4.05  #SimpNegUnit  : 443
% 10.53/4.05  #BackRed      : 127
% 10.53/4.05  
% 10.53/4.05  #Partial instantiations: 0
% 10.53/4.05  #Strategies tried      : 1
% 10.53/4.05  
% 10.53/4.05  Timing (in seconds)
% 10.53/4.05  ----------------------
% 10.53/4.05  Preprocessing        : 0.36
% 10.53/4.05  Parsing              : 0.20
% 10.53/4.05  CNF conversion       : 0.03
% 10.53/4.05  Main loop            : 2.84
% 10.53/4.05  Inferencing          : 0.71
% 10.53/4.05  Reduction            : 0.82
% 10.53/4.05  Demodulation         : 0.54
% 10.53/4.05  BG Simplification    : 0.07
% 10.53/4.05  Subsumption          : 1.05
% 10.53/4.05  Abstraction          : 0.10
% 10.53/4.05  MUC search           : 0.00
% 10.53/4.05  Cooper               : 0.00
% 10.53/4.05  Total                : 3.27
% 10.53/4.05  Index Insertion      : 0.00
% 10.53/4.06  Index Deletion       : 0.00
% 10.53/4.06  Index Matching       : 0.00
% 10.53/4.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
