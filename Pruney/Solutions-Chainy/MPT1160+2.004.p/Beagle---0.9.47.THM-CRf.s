%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:43 EST 2020

% Result     : Theorem 5.10s
% Output     : CNFRefutation 5.32s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 409 expanded)
%              Number of leaves         :   37 ( 161 expanded)
%              Depth                    :   19
%              Number of atoms          :  368 (1298 expanded)
%              Number of equality atoms :   33 ( 183 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k3_orders_2 > k2_orders_2 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_orders_2,type,(
    k3_orders_2: ( $i * $i * $i ) > $i )).

tff(k2_orders_2,type,(
    k2_orders_2: ( $i * $i ) > $i )).

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_174,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => k3_orders_2(A,k1_struct_0(A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_orders_2)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k1_struct_0(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_struct_0)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k3_orders_2(A,B,C),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_orders_2)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ~ ( B != k1_xboole_0
          & ! [C] :
              ( m1_subset_1(C,A)
             => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_157,axiom,(
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

tff(f_67,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_131,axiom,(
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
             => ~ ( r2_hidden(B,C)
                  & r2_hidden(B,k2_orders_2(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_orders_2)).

tff(f_75,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

tff(f_109,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => k2_orders_2(A,k2_struct_0(A)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_orders_2)).

tff(c_40,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_24,plain,(
    ! [A_18] :
      ( l1_struct_0(A_18)
      | ~ l1_orders_2(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_51,plain,(
    ! [A_45] :
      ( k1_struct_0(A_45) = k1_xboole_0
      | ~ l1_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_56,plain,(
    ! [A_46] :
      ( k1_struct_0(A_46) = k1_xboole_0
      | ~ l1_orders_2(A_46) ) ),
    inference(resolution,[status(thm)],[c_24,c_51])).

tff(c_60,plain,(
    k1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_56])).

tff(c_36,plain,(
    k3_orders_2('#skF_2',k1_struct_0('#skF_2'),'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_61,plain,(
    k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_36])).

tff(c_66,plain,(
    ! [A_47] :
      ( u1_struct_0(A_47) = k2_struct_0(A_47)
      | ~ l1_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_71,plain,(
    ! [A_48] :
      ( u1_struct_0(A_48) = k2_struct_0(A_48)
      | ~ l1_orders_2(A_48) ) ),
    inference(resolution,[status(thm)],[c_24,c_66])).

tff(c_75,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_71])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_77,plain,(
    m1_subset_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_38])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_46,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_44,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_42,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_6,plain,(
    ! [A_4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    ! [A_15,B_16,C_17] :
      ( m1_subset_1(k3_orders_2(A_15,B_16,C_17),k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ m1_subset_1(C_17,u1_struct_0(A_15))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_orders_2(A_15)
      | ~ v5_orders_2(A_15)
      | ~ v4_orders_2(A_15)
      | ~ v3_orders_2(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | k1_xboole_0 = B_2
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_270,plain,(
    ! [A_82,B_83,C_84] :
      ( m1_subset_1(k3_orders_2(A_82,B_83,C_84),k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ m1_subset_1(C_84,u1_struct_0(A_82))
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_orders_2(A_82)
      | ~ v5_orders_2(A_82)
      | ~ v4_orders_2(A_82)
      | ~ v3_orders_2(A_82)
      | v2_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_275,plain,(
    ! [B_83,C_84] :
      ( m1_subset_1(k3_orders_2('#skF_2',B_83,C_84),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(C_84,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_270])).

tff(c_278,plain,(
    ! [B_83,C_84] :
      ( m1_subset_1(k3_orders_2('#skF_2',B_83,C_84),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(C_84,k2_struct_0('#skF_2'))
      | ~ m1_subset_1(B_83,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_75,c_75,c_275])).

tff(c_291,plain,(
    ! [B_88,C_89] :
      ( m1_subset_1(k3_orders_2('#skF_2',B_88,C_89),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(C_89,k2_struct_0('#skF_2'))
      | ~ m1_subset_1(B_88,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_278])).

tff(c_10,plain,(
    ! [A_7,C_9,B_8] :
      ( m1_subset_1(A_7,C_9)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(C_9))
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_295,plain,(
    ! [A_90,B_91,C_92] :
      ( m1_subset_1(A_90,k2_struct_0('#skF_2'))
      | ~ r2_hidden(A_90,k3_orders_2('#skF_2',B_91,C_92))
      | ~ m1_subset_1(C_92,k2_struct_0('#skF_2'))
      | ~ m1_subset_1(B_91,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_291,c_10])).

tff(c_302,plain,(
    ! [A_1,B_91,C_92] :
      ( m1_subset_1('#skF_1'(A_1,k3_orders_2('#skF_2',B_91,C_92)),k2_struct_0('#skF_2'))
      | ~ m1_subset_1(C_92,k2_struct_0('#skF_2'))
      | ~ m1_subset_1(B_91,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_91,C_92) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_91,C_92),k1_zfmisc_1(A_1)) ) ),
    inference(resolution,[status(thm)],[c_2,c_295])).

tff(c_349,plain,(
    ! [B_101,D_102,A_103,C_104] :
      ( r2_hidden(B_101,D_102)
      | ~ r2_hidden(B_101,k3_orders_2(A_103,D_102,C_104))
      | ~ m1_subset_1(D_102,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ m1_subset_1(C_104,u1_struct_0(A_103))
      | ~ m1_subset_1(B_101,u1_struct_0(A_103))
      | ~ l1_orders_2(A_103)
      | ~ v5_orders_2(A_103)
      | ~ v4_orders_2(A_103)
      | ~ v3_orders_2(A_103)
      | v2_struct_0(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_1789,plain,(
    ! [A_321,A_322,D_323,C_324] :
      ( r2_hidden('#skF_1'(A_321,k3_orders_2(A_322,D_323,C_324)),D_323)
      | ~ m1_subset_1(D_323,k1_zfmisc_1(u1_struct_0(A_322)))
      | ~ m1_subset_1(C_324,u1_struct_0(A_322))
      | ~ m1_subset_1('#skF_1'(A_321,k3_orders_2(A_322,D_323,C_324)),u1_struct_0(A_322))
      | ~ l1_orders_2(A_322)
      | ~ v5_orders_2(A_322)
      | ~ v4_orders_2(A_322)
      | ~ v3_orders_2(A_322)
      | v2_struct_0(A_322)
      | k3_orders_2(A_322,D_323,C_324) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_322,D_323,C_324),k1_zfmisc_1(A_321)) ) ),
    inference(resolution,[status(thm)],[c_2,c_349])).

tff(c_1800,plain,(
    ! [A_321,D_323,C_324] :
      ( r2_hidden('#skF_1'(A_321,k3_orders_2('#skF_2',D_323,C_324)),D_323)
      | ~ m1_subset_1(D_323,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_324,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(A_321,k3_orders_2('#skF_2',D_323,C_324)),k2_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',D_323,C_324) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_323,C_324),k1_zfmisc_1(A_321)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_1789])).

tff(c_1805,plain,(
    ! [A_321,D_323,C_324] :
      ( r2_hidden('#skF_1'(A_321,k3_orders_2('#skF_2',D_323,C_324)),D_323)
      | ~ m1_subset_1(D_323,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(C_324,k2_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(A_321,k3_orders_2('#skF_2',D_323,C_324)),k2_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',D_323,C_324) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_323,C_324),k1_zfmisc_1(A_321)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_75,c_75,c_1800])).

tff(c_1807,plain,(
    ! [A_325,D_326,C_327] :
      ( r2_hidden('#skF_1'(A_325,k3_orders_2('#skF_2',D_326,C_327)),D_326)
      | ~ m1_subset_1(D_326,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(C_327,k2_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(A_325,k3_orders_2('#skF_2',D_326,C_327)),k2_struct_0('#skF_2'))
      | k3_orders_2('#skF_2',D_326,C_327) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_326,C_327),k1_zfmisc_1(A_325)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1805])).

tff(c_1815,plain,(
    ! [A_328,B_329,C_330] :
      ( r2_hidden('#skF_1'(A_328,k3_orders_2('#skF_2',B_329,C_330)),B_329)
      | ~ m1_subset_1(C_330,k2_struct_0('#skF_2'))
      | ~ m1_subset_1(B_329,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_329,C_330) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_329,C_330),k1_zfmisc_1(A_328)) ) ),
    inference(resolution,[status(thm)],[c_302,c_1807])).

tff(c_91,plain,(
    ! [A_51] :
      ( m1_subset_1(k2_struct_0(A_51),k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_94,plain,
    ( m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ l1_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_91])).

tff(c_96,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_99,plain,(
    ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_96])).

tff(c_103,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_99])).

tff(c_105,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r2_hidden(A_5,B_6)
      | v1_xboole_0(B_6)
      | ~ m1_subset_1(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1('#skF_1'(A_1,B_2),A_1)
      | k1_xboole_0 = B_2
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_104,plain,(
    m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_280,plain,(
    ! [B_85,A_86,C_87] :
      ( ~ r2_hidden(B_85,k2_orders_2(A_86,C_87))
      | ~ r2_hidden(B_85,C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ m1_subset_1(B_85,u1_struct_0(A_86))
      | ~ l1_orders_2(A_86)
      | ~ v5_orders_2(A_86)
      | ~ v4_orders_2(A_86)
      | ~ v3_orders_2(A_86)
      | v2_struct_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_391,plain,(
    ! [A_117,C_118,A_119] :
      ( ~ r2_hidden(A_117,C_118)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ m1_subset_1(A_117,u1_struct_0(A_119))
      | ~ l1_orders_2(A_119)
      | ~ v5_orders_2(A_119)
      | ~ v4_orders_2(A_119)
      | ~ v3_orders_2(A_119)
      | v2_struct_0(A_119)
      | v1_xboole_0(k2_orders_2(A_119,C_118))
      | ~ m1_subset_1(A_117,k2_orders_2(A_119,C_118)) ) ),
    inference(resolution,[status(thm)],[c_8,c_280])).

tff(c_405,plain,(
    ! [A_117,C_118] :
      ( ~ r2_hidden(A_117,C_118)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(A_117,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | v1_xboole_0(k2_orders_2('#skF_2',C_118))
      | ~ m1_subset_1(A_117,k2_orders_2('#skF_2',C_118)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_391])).

tff(c_415,plain,(
    ! [A_117,C_118] :
      ( ~ r2_hidden(A_117,C_118)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(A_117,k2_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | v1_xboole_0(k2_orders_2('#skF_2',C_118))
      | ~ m1_subset_1(A_117,k2_orders_2('#skF_2',C_118)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_75,c_405])).

tff(c_418,plain,(
    ! [A_120,C_121] :
      ( ~ r2_hidden(A_120,C_121)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(A_120,k2_struct_0('#skF_2'))
      | v1_xboole_0(k2_orders_2('#skF_2',C_121))
      | ~ m1_subset_1(A_120,k2_orders_2('#skF_2',C_121)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_415])).

tff(c_435,plain,(
    ! [A_120] :
      ( ~ r2_hidden(A_120,k2_struct_0('#skF_2'))
      | ~ m1_subset_1(A_120,k2_struct_0('#skF_2'))
      | v1_xboole_0(k2_orders_2('#skF_2',k2_struct_0('#skF_2')))
      | ~ m1_subset_1(A_120,k2_orders_2('#skF_2',k2_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_104,c_418])).

tff(c_459,plain,(
    ! [A_127] :
      ( ~ r2_hidden(A_127,k2_struct_0('#skF_2'))
      | ~ m1_subset_1(A_127,k2_struct_0('#skF_2'))
      | ~ m1_subset_1(A_127,k2_orders_2('#skF_2',k2_struct_0('#skF_2'))) ) ),
    inference(splitLeft,[status(thm)],[c_435])).

tff(c_689,plain,(
    ! [B_153] :
      ( ~ r2_hidden('#skF_1'(k2_orders_2('#skF_2',k2_struct_0('#skF_2')),B_153),k2_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(k2_orders_2('#skF_2',k2_struct_0('#skF_2')),B_153),k2_struct_0('#skF_2'))
      | k1_xboole_0 = B_153
      | ~ m1_subset_1(B_153,k1_zfmisc_1(k2_orders_2('#skF_2',k2_struct_0('#skF_2')))) ) ),
    inference(resolution,[status(thm)],[c_4,c_459])).

tff(c_706,plain,(
    ! [B_153] :
      ( k1_xboole_0 = B_153
      | ~ m1_subset_1(B_153,k1_zfmisc_1(k2_orders_2('#skF_2',k2_struct_0('#skF_2'))))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(k2_orders_2('#skF_2',k2_struct_0('#skF_2')),B_153),k2_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_8,c_689])).

tff(c_737,plain,(
    v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_706])).

tff(c_20,plain,(
    ! [A_14] :
      ( ~ v1_xboole_0(k2_struct_0(A_14))
      | ~ l1_struct_0(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_740,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_737,c_20])).

tff(c_743,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_740])).

tff(c_745,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_743])).

tff(c_747,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_706])).

tff(c_18,plain,(
    ! [A_13] :
      ( m1_subset_1(k2_struct_0(A_13),k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_116,plain,(
    ! [A_54,C_55,B_56] :
      ( m1_subset_1(A_54,C_55)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(C_55))
      | ~ r2_hidden(A_54,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_152,plain,(
    ! [A_62,A_63] :
      ( m1_subset_1(A_62,u1_struct_0(A_63))
      | ~ r2_hidden(A_62,k2_struct_0(A_63))
      | ~ l1_struct_0(A_63) ) ),
    inference(resolution,[status(thm)],[c_18,c_116])).

tff(c_157,plain,(
    ! [A_5,A_63] :
      ( m1_subset_1(A_5,u1_struct_0(A_63))
      | ~ l1_struct_0(A_63)
      | v1_xboole_0(k2_struct_0(A_63))
      | ~ m1_subset_1(A_5,k2_struct_0(A_63)) ) ),
    inference(resolution,[status(thm)],[c_8,c_152])).

tff(c_26,plain,(
    ! [A_19] :
      ( k2_orders_2(A_19,k2_struct_0(A_19)) = k1_xboole_0
      | ~ l1_orders_2(A_19)
      | ~ v5_orders_2(A_19)
      | ~ v4_orders_2(A_19)
      | ~ v3_orders_2(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_990,plain,(
    ! [B_197,A_198] :
      ( ~ r2_hidden(B_197,k1_xboole_0)
      | ~ r2_hidden(B_197,k2_struct_0(A_198))
      | ~ m1_subset_1(k2_struct_0(A_198),k1_zfmisc_1(u1_struct_0(A_198)))
      | ~ m1_subset_1(B_197,u1_struct_0(A_198))
      | ~ l1_orders_2(A_198)
      | ~ v5_orders_2(A_198)
      | ~ v4_orders_2(A_198)
      | ~ v3_orders_2(A_198)
      | v2_struct_0(A_198)
      | ~ l1_orders_2(A_198)
      | ~ v5_orders_2(A_198)
      | ~ v4_orders_2(A_198)
      | ~ v3_orders_2(A_198)
      | v2_struct_0(A_198) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_280])).

tff(c_999,plain,(
    ! [A_199,A_200] :
      ( ~ r2_hidden(A_199,k1_xboole_0)
      | ~ m1_subset_1(k2_struct_0(A_200),k1_zfmisc_1(u1_struct_0(A_200)))
      | ~ m1_subset_1(A_199,u1_struct_0(A_200))
      | ~ l1_orders_2(A_200)
      | ~ v5_orders_2(A_200)
      | ~ v4_orders_2(A_200)
      | ~ v3_orders_2(A_200)
      | v2_struct_0(A_200)
      | v1_xboole_0(k2_struct_0(A_200))
      | ~ m1_subset_1(A_199,k2_struct_0(A_200)) ) ),
    inference(resolution,[status(thm)],[c_8,c_990])).

tff(c_1056,plain,(
    ! [A_204,A_205] :
      ( ~ r2_hidden(A_204,k1_xboole_0)
      | ~ m1_subset_1(A_204,u1_struct_0(A_205))
      | ~ l1_orders_2(A_205)
      | ~ v5_orders_2(A_205)
      | ~ v4_orders_2(A_205)
      | ~ v3_orders_2(A_205)
      | v2_struct_0(A_205)
      | v1_xboole_0(k2_struct_0(A_205))
      | ~ m1_subset_1(A_204,k2_struct_0(A_205))
      | ~ l1_struct_0(A_205) ) ),
    inference(resolution,[status(thm)],[c_18,c_999])).

tff(c_1085,plain,(
    ! [A_206,A_207] :
      ( ~ r2_hidden(A_206,k1_xboole_0)
      | ~ l1_orders_2(A_207)
      | ~ v5_orders_2(A_207)
      | ~ v4_orders_2(A_207)
      | ~ v3_orders_2(A_207)
      | v2_struct_0(A_207)
      | ~ l1_struct_0(A_207)
      | v1_xboole_0(k2_struct_0(A_207))
      | ~ m1_subset_1(A_206,k2_struct_0(A_207)) ) ),
    inference(resolution,[status(thm)],[c_157,c_1056])).

tff(c_1088,plain,(
    ! [A_1,B_91,C_92] :
      ( ~ r2_hidden('#skF_1'(A_1,k3_orders_2('#skF_2',B_91,C_92)),k1_xboole_0)
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_2')
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ m1_subset_1(C_92,k2_struct_0('#skF_2'))
      | ~ m1_subset_1(B_91,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_91,C_92) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_91,C_92),k1_zfmisc_1(A_1)) ) ),
    inference(resolution,[status(thm)],[c_302,c_1085])).

tff(c_1105,plain,(
    ! [A_1,B_91,C_92] :
      ( ~ r2_hidden('#skF_1'(A_1,k3_orders_2('#skF_2',B_91,C_92)),k1_xboole_0)
      | v2_struct_0('#skF_2')
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ m1_subset_1(C_92,k2_struct_0('#skF_2'))
      | ~ m1_subset_1(B_91,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_91,C_92) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_91,C_92),k1_zfmisc_1(A_1)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_46,c_44,c_42,c_40,c_1088])).

tff(c_1106,plain,(
    ! [A_1,B_91,C_92] :
      ( ~ r2_hidden('#skF_1'(A_1,k3_orders_2('#skF_2',B_91,C_92)),k1_xboole_0)
      | ~ m1_subset_1(C_92,k2_struct_0('#skF_2'))
      | ~ m1_subset_1(B_91,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_91,C_92) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_91,C_92),k1_zfmisc_1(A_1)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_747,c_48,c_1105])).

tff(c_1822,plain,(
    ! [C_330,A_328] :
      ( ~ m1_subset_1(C_330,k2_struct_0('#skF_2'))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',k1_xboole_0,C_330) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',k1_xboole_0,C_330),k1_zfmisc_1(A_328)) ) ),
    inference(resolution,[status(thm)],[c_1815,c_1106])).

tff(c_1898,plain,(
    ! [C_331,A_332] :
      ( ~ m1_subset_1(C_331,k2_struct_0('#skF_2'))
      | k3_orders_2('#skF_2',k1_xboole_0,C_331) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',k1_xboole_0,C_331),k1_zfmisc_1(A_332)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1822])).

tff(c_1906,plain,(
    ! [C_17] :
      ( ~ m1_subset_1(C_17,k2_struct_0('#skF_2'))
      | k3_orders_2('#skF_2',k1_xboole_0,C_17) = k1_xboole_0
      | ~ m1_subset_1(C_17,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_22,c_1898])).

tff(c_1912,plain,(
    ! [C_17] :
      ( k3_orders_2('#skF_2',k1_xboole_0,C_17) = k1_xboole_0
      | ~ m1_subset_1(C_17,k2_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_6,c_75,c_75,c_1906])).

tff(c_1914,plain,(
    ! [C_333] :
      ( k3_orders_2('#skF_2',k1_xboole_0,C_333) = k1_xboole_0
      | ~ m1_subset_1(C_333,k2_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1912])).

tff(c_1931,plain,(
    k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_77,c_1914])).

tff(c_1939,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_1931])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n007.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 12:03:51 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.10/1.95  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.10/1.96  
% 5.10/1.96  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.10/1.96  %$ r2_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k3_orders_2 > k2_orders_2 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.10/1.96  
% 5.10/1.96  %Foreground sorts:
% 5.10/1.96  
% 5.10/1.96  
% 5.10/1.96  %Background operators:
% 5.10/1.96  
% 5.10/1.96  
% 5.10/1.96  %Foreground operators:
% 5.10/1.96  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.10/1.96  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 5.10/1.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.10/1.96  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.10/1.96  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.10/1.96  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 5.10/1.96  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 5.10/1.96  tff('#skF_2', type, '#skF_2': $i).
% 5.10/1.96  tff('#skF_3', type, '#skF_3': $i).
% 5.10/1.96  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 5.10/1.96  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 5.10/1.96  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.10/1.96  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.10/1.96  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 5.10/1.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.10/1.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.10/1.96  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 5.10/1.96  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 5.10/1.96  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.10/1.96  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.10/1.96  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 5.10/1.96  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.10/1.96  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.10/1.96  
% 5.32/1.98  tff(f_174, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k3_orders_2(A, k1_struct_0(A), B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_orders_2)).
% 5.32/1.98  tff(f_96, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 5.32/1.98  tff(f_55, axiom, (![A]: (l1_struct_0(A) => (k1_struct_0(A) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_struct_0)).
% 5.32/1.98  tff(f_59, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 5.32/1.98  tff(f_39, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 5.32/1.98  tff(f_92, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k3_orders_2(A, B, C), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 5.32/1.98  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_subset_1)).
% 5.32/1.98  tff(f_51, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 5.32/1.98  tff(f_157, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_orders_2)).
% 5.32/1.98  tff(f_67, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 5.32/1.98  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 5.32/1.98  tff(f_131, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r2_hidden(B, C) & r2_hidden(B, k2_orders_2(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_orders_2)).
% 5.32/1.98  tff(f_75, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_struct_0)).
% 5.32/1.98  tff(f_109, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k2_orders_2(A, k2_struct_0(A)) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_orders_2)).
% 5.32/1.98  tff(c_40, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_174])).
% 5.32/1.98  tff(c_24, plain, (![A_18]: (l1_struct_0(A_18) | ~l1_orders_2(A_18))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.32/1.98  tff(c_51, plain, (![A_45]: (k1_struct_0(A_45)=k1_xboole_0 | ~l1_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.32/1.98  tff(c_56, plain, (![A_46]: (k1_struct_0(A_46)=k1_xboole_0 | ~l1_orders_2(A_46))), inference(resolution, [status(thm)], [c_24, c_51])).
% 5.32/1.98  tff(c_60, plain, (k1_struct_0('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_56])).
% 5.32/1.98  tff(c_36, plain, (k3_orders_2('#skF_2', k1_struct_0('#skF_2'), '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_174])).
% 5.32/1.98  tff(c_61, plain, (k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_60, c_36])).
% 5.32/1.98  tff(c_66, plain, (![A_47]: (u1_struct_0(A_47)=k2_struct_0(A_47) | ~l1_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.32/1.98  tff(c_71, plain, (![A_48]: (u1_struct_0(A_48)=k2_struct_0(A_48) | ~l1_orders_2(A_48))), inference(resolution, [status(thm)], [c_24, c_66])).
% 5.32/1.98  tff(c_75, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_71])).
% 5.32/1.98  tff(c_38, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_174])).
% 5.32/1.98  tff(c_77, plain, (m1_subset_1('#skF_3', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_38])).
% 5.32/1.98  tff(c_48, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_174])).
% 5.32/1.98  tff(c_46, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_174])).
% 5.32/1.98  tff(c_44, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_174])).
% 5.32/1.98  tff(c_42, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_174])).
% 5.32/1.98  tff(c_6, plain, (![A_4]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.32/1.98  tff(c_22, plain, (![A_15, B_16, C_17]: (m1_subset_1(k3_orders_2(A_15, B_16, C_17), k1_zfmisc_1(u1_struct_0(A_15))) | ~m1_subset_1(C_17, u1_struct_0(A_15)) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_orders_2(A_15) | ~v5_orders_2(A_15) | ~v4_orders_2(A_15) | ~v3_orders_2(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.32/1.98  tff(c_2, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | k1_xboole_0=B_2 | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.32/1.98  tff(c_270, plain, (![A_82, B_83, C_84]: (m1_subset_1(k3_orders_2(A_82, B_83, C_84), k1_zfmisc_1(u1_struct_0(A_82))) | ~m1_subset_1(C_84, u1_struct_0(A_82)) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_orders_2(A_82) | ~v5_orders_2(A_82) | ~v4_orders_2(A_82) | ~v3_orders_2(A_82) | v2_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.32/1.98  tff(c_275, plain, (![B_83, C_84]: (m1_subset_1(k3_orders_2('#skF_2', B_83, C_84), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(C_84, u1_struct_0('#skF_2')) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_75, c_270])).
% 5.32/1.98  tff(c_278, plain, (![B_83, C_84]: (m1_subset_1(k3_orders_2('#skF_2', B_83, C_84), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(C_84, k2_struct_0('#skF_2')) | ~m1_subset_1(B_83, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_75, c_75, c_275])).
% 5.32/1.98  tff(c_291, plain, (![B_88, C_89]: (m1_subset_1(k3_orders_2('#skF_2', B_88, C_89), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(C_89, k2_struct_0('#skF_2')) | ~m1_subset_1(B_88, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_48, c_278])).
% 5.32/1.98  tff(c_10, plain, (![A_7, C_9, B_8]: (m1_subset_1(A_7, C_9) | ~m1_subset_1(B_8, k1_zfmisc_1(C_9)) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.32/1.98  tff(c_295, plain, (![A_90, B_91, C_92]: (m1_subset_1(A_90, k2_struct_0('#skF_2')) | ~r2_hidden(A_90, k3_orders_2('#skF_2', B_91, C_92)) | ~m1_subset_1(C_92, k2_struct_0('#skF_2')) | ~m1_subset_1(B_91, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_291, c_10])).
% 5.32/1.98  tff(c_302, plain, (![A_1, B_91, C_92]: (m1_subset_1('#skF_1'(A_1, k3_orders_2('#skF_2', B_91, C_92)), k2_struct_0('#skF_2')) | ~m1_subset_1(C_92, k2_struct_0('#skF_2')) | ~m1_subset_1(B_91, k1_zfmisc_1(k2_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_91, C_92)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', B_91, C_92), k1_zfmisc_1(A_1)))), inference(resolution, [status(thm)], [c_2, c_295])).
% 5.32/1.98  tff(c_349, plain, (![B_101, D_102, A_103, C_104]: (r2_hidden(B_101, D_102) | ~r2_hidden(B_101, k3_orders_2(A_103, D_102, C_104)) | ~m1_subset_1(D_102, k1_zfmisc_1(u1_struct_0(A_103))) | ~m1_subset_1(C_104, u1_struct_0(A_103)) | ~m1_subset_1(B_101, u1_struct_0(A_103)) | ~l1_orders_2(A_103) | ~v5_orders_2(A_103) | ~v4_orders_2(A_103) | ~v3_orders_2(A_103) | v2_struct_0(A_103))), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.32/1.98  tff(c_1789, plain, (![A_321, A_322, D_323, C_324]: (r2_hidden('#skF_1'(A_321, k3_orders_2(A_322, D_323, C_324)), D_323) | ~m1_subset_1(D_323, k1_zfmisc_1(u1_struct_0(A_322))) | ~m1_subset_1(C_324, u1_struct_0(A_322)) | ~m1_subset_1('#skF_1'(A_321, k3_orders_2(A_322, D_323, C_324)), u1_struct_0(A_322)) | ~l1_orders_2(A_322) | ~v5_orders_2(A_322) | ~v4_orders_2(A_322) | ~v3_orders_2(A_322) | v2_struct_0(A_322) | k3_orders_2(A_322, D_323, C_324)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_322, D_323, C_324), k1_zfmisc_1(A_321)))), inference(resolution, [status(thm)], [c_2, c_349])).
% 5.32/1.98  tff(c_1800, plain, (![A_321, D_323, C_324]: (r2_hidden('#skF_1'(A_321, k3_orders_2('#skF_2', D_323, C_324)), D_323) | ~m1_subset_1(D_323, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_324, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(A_321, k3_orders_2('#skF_2', D_323, C_324)), k2_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', D_323, C_324)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', D_323, C_324), k1_zfmisc_1(A_321)))), inference(superposition, [status(thm), theory('equality')], [c_75, c_1789])).
% 5.32/1.98  tff(c_1805, plain, (![A_321, D_323, C_324]: (r2_hidden('#skF_1'(A_321, k3_orders_2('#skF_2', D_323, C_324)), D_323) | ~m1_subset_1(D_323, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(C_324, k2_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(A_321, k3_orders_2('#skF_2', D_323, C_324)), k2_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', D_323, C_324)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', D_323, C_324), k1_zfmisc_1(A_321)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_75, c_75, c_1800])).
% 5.32/1.98  tff(c_1807, plain, (![A_325, D_326, C_327]: (r2_hidden('#skF_1'(A_325, k3_orders_2('#skF_2', D_326, C_327)), D_326) | ~m1_subset_1(D_326, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(C_327, k2_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(A_325, k3_orders_2('#skF_2', D_326, C_327)), k2_struct_0('#skF_2')) | k3_orders_2('#skF_2', D_326, C_327)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', D_326, C_327), k1_zfmisc_1(A_325)))), inference(negUnitSimplification, [status(thm)], [c_48, c_1805])).
% 5.32/1.98  tff(c_1815, plain, (![A_328, B_329, C_330]: (r2_hidden('#skF_1'(A_328, k3_orders_2('#skF_2', B_329, C_330)), B_329) | ~m1_subset_1(C_330, k2_struct_0('#skF_2')) | ~m1_subset_1(B_329, k1_zfmisc_1(k2_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_329, C_330)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', B_329, C_330), k1_zfmisc_1(A_328)))), inference(resolution, [status(thm)], [c_302, c_1807])).
% 5.32/1.98  tff(c_91, plain, (![A_51]: (m1_subset_1(k2_struct_0(A_51), k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.32/1.98  tff(c_94, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_75, c_91])).
% 5.32/1.98  tff(c_96, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_94])).
% 5.32/1.98  tff(c_99, plain, (~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_24, c_96])).
% 5.32/1.98  tff(c_103, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_99])).
% 5.32/1.98  tff(c_105, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_94])).
% 5.32/1.98  tff(c_8, plain, (![A_5, B_6]: (r2_hidden(A_5, B_6) | v1_xboole_0(B_6) | ~m1_subset_1(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.32/1.98  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1('#skF_1'(A_1, B_2), A_1) | k1_xboole_0=B_2 | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.32/1.98  tff(c_104, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_94])).
% 5.32/1.98  tff(c_280, plain, (![B_85, A_86, C_87]: (~r2_hidden(B_85, k2_orders_2(A_86, C_87)) | ~r2_hidden(B_85, C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(u1_struct_0(A_86))) | ~m1_subset_1(B_85, u1_struct_0(A_86)) | ~l1_orders_2(A_86) | ~v5_orders_2(A_86) | ~v4_orders_2(A_86) | ~v3_orders_2(A_86) | v2_struct_0(A_86))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.32/1.98  tff(c_391, plain, (![A_117, C_118, A_119]: (~r2_hidden(A_117, C_118) | ~m1_subset_1(C_118, k1_zfmisc_1(u1_struct_0(A_119))) | ~m1_subset_1(A_117, u1_struct_0(A_119)) | ~l1_orders_2(A_119) | ~v5_orders_2(A_119) | ~v4_orders_2(A_119) | ~v3_orders_2(A_119) | v2_struct_0(A_119) | v1_xboole_0(k2_orders_2(A_119, C_118)) | ~m1_subset_1(A_117, k2_orders_2(A_119, C_118)))), inference(resolution, [status(thm)], [c_8, c_280])).
% 5.32/1.98  tff(c_405, plain, (![A_117, C_118]: (~r2_hidden(A_117, C_118) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(A_117, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | v1_xboole_0(k2_orders_2('#skF_2', C_118)) | ~m1_subset_1(A_117, k2_orders_2('#skF_2', C_118)))), inference(superposition, [status(thm), theory('equality')], [c_75, c_391])).
% 5.32/1.98  tff(c_415, plain, (![A_117, C_118]: (~r2_hidden(A_117, C_118) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(A_117, k2_struct_0('#skF_2')) | v2_struct_0('#skF_2') | v1_xboole_0(k2_orders_2('#skF_2', C_118)) | ~m1_subset_1(A_117, k2_orders_2('#skF_2', C_118)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_75, c_405])).
% 5.32/1.98  tff(c_418, plain, (![A_120, C_121]: (~r2_hidden(A_120, C_121) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(A_120, k2_struct_0('#skF_2')) | v1_xboole_0(k2_orders_2('#skF_2', C_121)) | ~m1_subset_1(A_120, k2_orders_2('#skF_2', C_121)))), inference(negUnitSimplification, [status(thm)], [c_48, c_415])).
% 5.32/1.98  tff(c_435, plain, (![A_120]: (~r2_hidden(A_120, k2_struct_0('#skF_2')) | ~m1_subset_1(A_120, k2_struct_0('#skF_2')) | v1_xboole_0(k2_orders_2('#skF_2', k2_struct_0('#skF_2'))) | ~m1_subset_1(A_120, k2_orders_2('#skF_2', k2_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_104, c_418])).
% 5.32/1.98  tff(c_459, plain, (![A_127]: (~r2_hidden(A_127, k2_struct_0('#skF_2')) | ~m1_subset_1(A_127, k2_struct_0('#skF_2')) | ~m1_subset_1(A_127, k2_orders_2('#skF_2', k2_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_435])).
% 5.32/1.98  tff(c_689, plain, (![B_153]: (~r2_hidden('#skF_1'(k2_orders_2('#skF_2', k2_struct_0('#skF_2')), B_153), k2_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(k2_orders_2('#skF_2', k2_struct_0('#skF_2')), B_153), k2_struct_0('#skF_2')) | k1_xboole_0=B_153 | ~m1_subset_1(B_153, k1_zfmisc_1(k2_orders_2('#skF_2', k2_struct_0('#skF_2')))))), inference(resolution, [status(thm)], [c_4, c_459])).
% 5.32/1.98  tff(c_706, plain, (![B_153]: (k1_xboole_0=B_153 | ~m1_subset_1(B_153, k1_zfmisc_1(k2_orders_2('#skF_2', k2_struct_0('#skF_2')))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(k2_orders_2('#skF_2', k2_struct_0('#skF_2')), B_153), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_8, c_689])).
% 5.32/1.98  tff(c_737, plain, (v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_706])).
% 5.32/1.98  tff(c_20, plain, (![A_14]: (~v1_xboole_0(k2_struct_0(A_14)) | ~l1_struct_0(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.32/1.98  tff(c_740, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_737, c_20])).
% 5.32/1.98  tff(c_743, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_740])).
% 5.32/1.98  tff(c_745, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_743])).
% 5.32/1.98  tff(c_747, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_706])).
% 5.32/1.98  tff(c_18, plain, (![A_13]: (m1_subset_1(k2_struct_0(A_13), k1_zfmisc_1(u1_struct_0(A_13))) | ~l1_struct_0(A_13))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.32/1.98  tff(c_116, plain, (![A_54, C_55, B_56]: (m1_subset_1(A_54, C_55) | ~m1_subset_1(B_56, k1_zfmisc_1(C_55)) | ~r2_hidden(A_54, B_56))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.32/1.98  tff(c_152, plain, (![A_62, A_63]: (m1_subset_1(A_62, u1_struct_0(A_63)) | ~r2_hidden(A_62, k2_struct_0(A_63)) | ~l1_struct_0(A_63))), inference(resolution, [status(thm)], [c_18, c_116])).
% 5.32/1.98  tff(c_157, plain, (![A_5, A_63]: (m1_subset_1(A_5, u1_struct_0(A_63)) | ~l1_struct_0(A_63) | v1_xboole_0(k2_struct_0(A_63)) | ~m1_subset_1(A_5, k2_struct_0(A_63)))), inference(resolution, [status(thm)], [c_8, c_152])).
% 5.32/1.98  tff(c_26, plain, (![A_19]: (k2_orders_2(A_19, k2_struct_0(A_19))=k1_xboole_0 | ~l1_orders_2(A_19) | ~v5_orders_2(A_19) | ~v4_orders_2(A_19) | ~v3_orders_2(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.32/1.98  tff(c_990, plain, (![B_197, A_198]: (~r2_hidden(B_197, k1_xboole_0) | ~r2_hidden(B_197, k2_struct_0(A_198)) | ~m1_subset_1(k2_struct_0(A_198), k1_zfmisc_1(u1_struct_0(A_198))) | ~m1_subset_1(B_197, u1_struct_0(A_198)) | ~l1_orders_2(A_198) | ~v5_orders_2(A_198) | ~v4_orders_2(A_198) | ~v3_orders_2(A_198) | v2_struct_0(A_198) | ~l1_orders_2(A_198) | ~v5_orders_2(A_198) | ~v4_orders_2(A_198) | ~v3_orders_2(A_198) | v2_struct_0(A_198))), inference(superposition, [status(thm), theory('equality')], [c_26, c_280])).
% 5.32/1.98  tff(c_999, plain, (![A_199, A_200]: (~r2_hidden(A_199, k1_xboole_0) | ~m1_subset_1(k2_struct_0(A_200), k1_zfmisc_1(u1_struct_0(A_200))) | ~m1_subset_1(A_199, u1_struct_0(A_200)) | ~l1_orders_2(A_200) | ~v5_orders_2(A_200) | ~v4_orders_2(A_200) | ~v3_orders_2(A_200) | v2_struct_0(A_200) | v1_xboole_0(k2_struct_0(A_200)) | ~m1_subset_1(A_199, k2_struct_0(A_200)))), inference(resolution, [status(thm)], [c_8, c_990])).
% 5.32/1.98  tff(c_1056, plain, (![A_204, A_205]: (~r2_hidden(A_204, k1_xboole_0) | ~m1_subset_1(A_204, u1_struct_0(A_205)) | ~l1_orders_2(A_205) | ~v5_orders_2(A_205) | ~v4_orders_2(A_205) | ~v3_orders_2(A_205) | v2_struct_0(A_205) | v1_xboole_0(k2_struct_0(A_205)) | ~m1_subset_1(A_204, k2_struct_0(A_205)) | ~l1_struct_0(A_205))), inference(resolution, [status(thm)], [c_18, c_999])).
% 5.32/1.98  tff(c_1085, plain, (![A_206, A_207]: (~r2_hidden(A_206, k1_xboole_0) | ~l1_orders_2(A_207) | ~v5_orders_2(A_207) | ~v4_orders_2(A_207) | ~v3_orders_2(A_207) | v2_struct_0(A_207) | ~l1_struct_0(A_207) | v1_xboole_0(k2_struct_0(A_207)) | ~m1_subset_1(A_206, k2_struct_0(A_207)))), inference(resolution, [status(thm)], [c_157, c_1056])).
% 5.32/1.98  tff(c_1088, plain, (![A_1, B_91, C_92]: (~r2_hidden('#skF_1'(A_1, k3_orders_2('#skF_2', B_91, C_92)), k1_xboole_0) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0('#skF_2') | v1_xboole_0(k2_struct_0('#skF_2')) | ~m1_subset_1(C_92, k2_struct_0('#skF_2')) | ~m1_subset_1(B_91, k1_zfmisc_1(k2_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_91, C_92)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', B_91, C_92), k1_zfmisc_1(A_1)))), inference(resolution, [status(thm)], [c_302, c_1085])).
% 5.32/1.98  tff(c_1105, plain, (![A_1, B_91, C_92]: (~r2_hidden('#skF_1'(A_1, k3_orders_2('#skF_2', B_91, C_92)), k1_xboole_0) | v2_struct_0('#skF_2') | v1_xboole_0(k2_struct_0('#skF_2')) | ~m1_subset_1(C_92, k2_struct_0('#skF_2')) | ~m1_subset_1(B_91, k1_zfmisc_1(k2_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_91, C_92)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', B_91, C_92), k1_zfmisc_1(A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_46, c_44, c_42, c_40, c_1088])).
% 5.32/1.98  tff(c_1106, plain, (![A_1, B_91, C_92]: (~r2_hidden('#skF_1'(A_1, k3_orders_2('#skF_2', B_91, C_92)), k1_xboole_0) | ~m1_subset_1(C_92, k2_struct_0('#skF_2')) | ~m1_subset_1(B_91, k1_zfmisc_1(k2_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_91, C_92)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', B_91, C_92), k1_zfmisc_1(A_1)))), inference(negUnitSimplification, [status(thm)], [c_747, c_48, c_1105])).
% 5.32/1.98  tff(c_1822, plain, (![C_330, A_328]: (~m1_subset_1(C_330, k2_struct_0('#skF_2')) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_struct_0('#skF_2'))) | k3_orders_2('#skF_2', k1_xboole_0, C_330)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', k1_xboole_0, C_330), k1_zfmisc_1(A_328)))), inference(resolution, [status(thm)], [c_1815, c_1106])).
% 5.32/1.98  tff(c_1898, plain, (![C_331, A_332]: (~m1_subset_1(C_331, k2_struct_0('#skF_2')) | k3_orders_2('#skF_2', k1_xboole_0, C_331)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', k1_xboole_0, C_331), k1_zfmisc_1(A_332)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1822])).
% 5.32/1.98  tff(c_1906, plain, (![C_17]: (~m1_subset_1(C_17, k2_struct_0('#skF_2')) | k3_orders_2('#skF_2', k1_xboole_0, C_17)=k1_xboole_0 | ~m1_subset_1(C_17, u1_struct_0('#skF_2')) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_22, c_1898])).
% 5.32/1.98  tff(c_1912, plain, (![C_17]: (k3_orders_2('#skF_2', k1_xboole_0, C_17)=k1_xboole_0 | ~m1_subset_1(C_17, k2_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_6, c_75, c_75, c_1906])).
% 5.32/1.98  tff(c_1914, plain, (![C_333]: (k3_orders_2('#skF_2', k1_xboole_0, C_333)=k1_xboole_0 | ~m1_subset_1(C_333, k2_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_48, c_1912])).
% 5.32/1.98  tff(c_1931, plain, (k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_77, c_1914])).
% 5.32/1.98  tff(c_1939, plain, $false, inference(negUnitSimplification, [status(thm)], [c_61, c_1931])).
% 5.32/1.98  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.32/1.98  
% 5.32/1.98  Inference rules
% 5.32/1.98  ----------------------
% 5.32/1.98  #Ref     : 0
% 5.32/1.98  #Sup     : 383
% 5.32/1.98  #Fact    : 0
% 5.32/1.98  #Define  : 0
% 5.32/1.98  #Split   : 11
% 5.32/1.98  #Chain   : 0
% 5.32/1.98  #Close   : 0
% 5.32/1.98  
% 5.32/1.98  Ordering : KBO
% 5.32/1.98  
% 5.32/1.98  Simplification rules
% 5.32/1.98  ----------------------
% 5.32/1.98  #Subsume      : 81
% 5.32/1.98  #Demod        : 389
% 5.32/1.98  #Tautology    : 46
% 5.32/1.98  #SimpNegUnit  : 65
% 5.32/1.98  #BackRed      : 6
% 5.32/1.98  
% 5.32/1.98  #Partial instantiations: 0
% 5.32/1.98  #Strategies tried      : 1
% 5.32/1.98  
% 5.32/1.98  Timing (in seconds)
% 5.32/1.98  ----------------------
% 5.32/1.98  Preprocessing        : 0.35
% 5.32/1.98  Parsing              : 0.19
% 5.32/1.98  CNF conversion       : 0.03
% 5.32/1.98  Main loop            : 0.86
% 5.32/1.98  Inferencing          : 0.28
% 5.32/1.98  Reduction            : 0.24
% 5.32/1.98  Demodulation         : 0.16
% 5.32/1.98  BG Simplification    : 0.03
% 5.32/1.98  Subsumption          : 0.24
% 5.32/1.98  Abstraction          : 0.04
% 5.32/1.98  MUC search           : 0.00
% 5.32/1.99  Cooper               : 0.00
% 5.32/1.99  Total                : 1.25
% 5.32/1.99  Index Insertion      : 0.00
% 5.32/1.99  Index Deletion       : 0.00
% 5.32/1.99  Index Matching       : 0.00
% 5.32/1.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
