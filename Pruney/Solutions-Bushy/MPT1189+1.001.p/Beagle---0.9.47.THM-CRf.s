%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1189+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:33 EST 2020

% Result     : Theorem 4.36s
% Output     : CNFRefutation 4.52s
% Verified   : 
% Statistics : Number of formulae       :  183 (1702 expanded)
%              Number of leaves         :   47 ( 623 expanded)
%              Depth                    :   27
%              Number of atoms          :  549 (7608 expanded)
%              Number of equality atoms :   59 ( 743 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r1_orders_2 > v1_partfun1 > r9_orders_1 > r2_hidden > m1_subset_1 > v8_relat_2 > v5_orders_2 > v4_relat_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_orders_2 > v1_xboole_0 > v1_relat_2 > v1_relat_1 > l1_struct_0 > l1_orders_2 > k4_tarski > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k3_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(v1_relat_2,type,(
    v1_relat_2: $i > $o )).

tff(v8_relat_2,type,(
    v8_relat_2: $i > $o )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(v4_relat_2,type,(
    v4_relat_2: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(r9_orders_1,type,(
    r9_orders_1: ( $i * $i ) > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v2_orders_2,type,(
    v2_orders_2: $i > $o )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_166,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( r9_orders_1(u1_orders_2(A),B)
            <=> ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ( B != C
                   => r2_orders_2(A,B,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t161_orders_2)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_141,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_30,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v3_orders_2(A)
       => v2_orders_2(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_orders_2)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_103,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & l1_orders_2(A) )
     => v1_relat_2(u1_orders_2(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_orders_2)).

tff(f_111,axiom,(
    ! [A] :
      ( ( v2_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => v4_relat_2(u1_orders_2(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_orders_2)).

tff(f_119,axiom,(
    ! [A] :
      ( ( v2_orders_2(A)
        & v4_orders_2(A)
        & l1_orders_2(A) )
     => v8_relat_2(u1_orders_2(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_orders_2)).

tff(f_89,axiom,(
    ! [A] :
      ( ( v2_orders_2(A)
        & l1_orders_2(A) )
     => v1_partfun1(u1_orders_2(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_orders_2)).

tff(f_131,axiom,(
    ! [A,B] :
      ( ( v1_relat_2(B)
        & v4_relat_2(B)
        & v8_relat_2(B)
        & v1_partfun1(B,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k3_relat_1(B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_orders_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r9_orders_1(A,B)
        <=> ( r2_hidden(B,k3_relat_1(A))
            & ! [C] :
                ( r2_hidden(C,k3_relat_1(A))
               => ( C = B
                  | r2_hidden(k4_tarski(B,C),A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_orders_1)).

tff(f_135,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_49,axiom,(
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

tff(f_75,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_orders_2(A,B,C)
              <=> r2_hidden(k4_tarski(B,C),u1_orders_2(A)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).

tff(f_97,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_48,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_26,plain,(
    ! [A_29] :
      ( l1_struct_0(A_29)
      | ~ l1_orders_2(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_44,plain,(
    ! [A_40,B_41] :
      ( r2_hidden(A_40,B_41)
      | v1_xboole_0(B_41)
      | ~ m1_subset_1(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_60,plain,
    ( '#skF_3' != '#skF_4'
    | ~ r9_orders_1(u1_orders_2('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_82,plain,(
    ~ r9_orders_1(u1_orders_2('#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_54,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_75,plain,(
    ! [A_53] :
      ( v2_orders_2(A_53)
      | ~ v3_orders_2(A_53)
      | ~ l1_orders_2(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_78,plain,
    ( v2_orders_2('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_75])).

tff(c_81,plain,(
    v2_orders_2('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_78])).

tff(c_50,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_52,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_102,plain,(
    ! [A_70] :
      ( m1_subset_1(u1_orders_2(A_70),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_70),u1_struct_0(A_70))))
      | ~ l1_orders_2(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_4,plain,(
    ! [C_4,A_2,B_3] :
      ( v1_relat_1(C_4)
      | ~ m1_subset_1(C_4,k1_zfmisc_1(k2_zfmisc_1(A_2,B_3))) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_106,plain,(
    ! [A_70] :
      ( v1_relat_1(u1_orders_2(A_70))
      | ~ l1_orders_2(A_70) ) ),
    inference(resolution,[status(thm)],[c_102,c_4])).

tff(c_34,plain,(
    ! [A_33] :
      ( v1_relat_2(u1_orders_2(A_33))
      | ~ l1_orders_2(A_33)
      | ~ v3_orders_2(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_36,plain,(
    ! [A_34] :
      ( v4_relat_2(u1_orders_2(A_34))
      | ~ l1_orders_2(A_34)
      | ~ v5_orders_2(A_34)
      | ~ v2_orders_2(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_38,plain,(
    ! [A_35] :
      ( v8_relat_2(u1_orders_2(A_35))
      | ~ l1_orders_2(A_35)
      | ~ v4_orders_2(A_35)
      | ~ v2_orders_2(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_30,plain,(
    ! [A_31] :
      ( v1_partfun1(u1_orders_2(A_31),u1_struct_0(A_31))
      | ~ l1_orders_2(A_31)
      | ~ v2_orders_2(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_28,plain,(
    ! [A_30] :
      ( m1_subset_1(u1_orders_2(A_30),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_30),u1_struct_0(A_30))))
      | ~ l1_orders_2(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_202,plain,(
    ! [B_92,A_93] :
      ( k3_relat_1(B_92) = A_93
      | ~ m1_subset_1(B_92,k1_zfmisc_1(k2_zfmisc_1(A_93,A_93)))
      | ~ v1_partfun1(B_92,A_93)
      | ~ v8_relat_2(B_92)
      | ~ v4_relat_2(B_92)
      | ~ v1_relat_2(B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_310,plain,(
    ! [A_115] :
      ( k3_relat_1(u1_orders_2(A_115)) = u1_struct_0(A_115)
      | ~ v1_partfun1(u1_orders_2(A_115),u1_struct_0(A_115))
      | ~ v8_relat_2(u1_orders_2(A_115))
      | ~ v4_relat_2(u1_orders_2(A_115))
      | ~ v1_relat_2(u1_orders_2(A_115))
      | ~ l1_orders_2(A_115) ) ),
    inference(resolution,[status(thm)],[c_28,c_202])).

tff(c_315,plain,(
    ! [A_116] :
      ( k3_relat_1(u1_orders_2(A_116)) = u1_struct_0(A_116)
      | ~ v8_relat_2(u1_orders_2(A_116))
      | ~ v4_relat_2(u1_orders_2(A_116))
      | ~ v1_relat_2(u1_orders_2(A_116))
      | ~ l1_orders_2(A_116)
      | ~ v2_orders_2(A_116) ) ),
    inference(resolution,[status(thm)],[c_30,c_310])).

tff(c_320,plain,(
    ! [A_117] :
      ( k3_relat_1(u1_orders_2(A_117)) = u1_struct_0(A_117)
      | ~ v4_relat_2(u1_orders_2(A_117))
      | ~ v1_relat_2(u1_orders_2(A_117))
      | ~ l1_orders_2(A_117)
      | ~ v4_orders_2(A_117)
      | ~ v2_orders_2(A_117) ) ),
    inference(resolution,[status(thm)],[c_38,c_315])).

tff(c_325,plain,(
    ! [A_118] :
      ( k3_relat_1(u1_orders_2(A_118)) = u1_struct_0(A_118)
      | ~ v1_relat_2(u1_orders_2(A_118))
      | ~ v4_orders_2(A_118)
      | ~ l1_orders_2(A_118)
      | ~ v5_orders_2(A_118)
      | ~ v2_orders_2(A_118) ) ),
    inference(resolution,[status(thm)],[c_36,c_320])).

tff(c_330,plain,(
    ! [A_119] :
      ( k3_relat_1(u1_orders_2(A_119)) = u1_struct_0(A_119)
      | ~ v4_orders_2(A_119)
      | ~ v5_orders_2(A_119)
      | ~ v2_orders_2(A_119)
      | ~ l1_orders_2(A_119)
      | ~ v3_orders_2(A_119) ) ),
    inference(resolution,[status(thm)],[c_34,c_325])).

tff(c_18,plain,(
    ! [A_12,B_18] :
      ( '#skF_1'(A_12,B_18) != B_18
      | r9_orders_1(A_12,B_18)
      | ~ r2_hidden(B_18,k3_relat_1(A_12))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_436,plain,(
    ! [A_138,B_139] :
      ( '#skF_1'(u1_orders_2(A_138),B_139) != B_139
      | r9_orders_1(u1_orders_2(A_138),B_139)
      | ~ r2_hidden(B_139,u1_struct_0(A_138))
      | ~ v1_relat_1(u1_orders_2(A_138))
      | ~ v4_orders_2(A_138)
      | ~ v5_orders_2(A_138)
      | ~ v2_orders_2(A_138)
      | ~ l1_orders_2(A_138)
      | ~ v3_orders_2(A_138) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_330,c_18])).

tff(c_449,plain,
    ( '#skF_1'(u1_orders_2('#skF_2'),'#skF_3') != '#skF_3'
    | ~ r2_hidden('#skF_3',u1_struct_0('#skF_2'))
    | ~ v1_relat_1(u1_orders_2('#skF_2'))
    | ~ v4_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v2_orders_2('#skF_2')
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_436,c_82])).

tff(c_455,plain,
    ( '#skF_1'(u1_orders_2('#skF_2'),'#skF_3') != '#skF_3'
    | ~ r2_hidden('#skF_3',u1_struct_0('#skF_2'))
    | ~ v1_relat_1(u1_orders_2('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_81,c_50,c_52,c_449])).

tff(c_475,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_455])).

tff(c_478,plain,(
    ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_106,c_475])).

tff(c_482,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_478])).

tff(c_484,plain,(
    v1_relat_1(u1_orders_2('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_455])).

tff(c_329,plain,(
    ! [A_33] :
      ( k3_relat_1(u1_orders_2(A_33)) = u1_struct_0(A_33)
      | ~ v4_orders_2(A_33)
      | ~ v5_orders_2(A_33)
      | ~ v2_orders_2(A_33)
      | ~ l1_orders_2(A_33)
      | ~ v3_orders_2(A_33) ) ),
    inference(resolution,[status(thm)],[c_34,c_325])).

tff(c_483,plain,
    ( ~ r2_hidden('#skF_3',u1_struct_0('#skF_2'))
    | '#skF_1'(u1_orders_2('#skF_2'),'#skF_3') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_455])).

tff(c_485,plain,(
    '#skF_1'(u1_orders_2('#skF_2'),'#skF_3') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_483])).

tff(c_125,plain,(
    ! [A_75,B_76] :
      ( r2_hidden('#skF_1'(A_75,B_76),k3_relat_1(A_75))
      | r9_orders_1(A_75,B_76)
      | ~ r2_hidden(B_76,k3_relat_1(A_75))
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_42,plain,(
    ! [A_38,B_39] :
      ( m1_subset_1(A_38,B_39)
      | ~ r2_hidden(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_133,plain,(
    ! [A_75,B_76] :
      ( m1_subset_1('#skF_1'(A_75,B_76),k3_relat_1(A_75))
      | r9_orders_1(A_75,B_76)
      | ~ r2_hidden(B_76,k3_relat_1(A_75))
      | ~ v1_relat_1(A_75) ) ),
    inference(resolution,[status(thm)],[c_125,c_42])).

tff(c_341,plain,(
    ! [A_119,B_76] :
      ( m1_subset_1('#skF_1'(u1_orders_2(A_119),B_76),u1_struct_0(A_119))
      | r9_orders_1(u1_orders_2(A_119),B_76)
      | ~ r2_hidden(B_76,k3_relat_1(u1_orders_2(A_119)))
      | ~ v1_relat_1(u1_orders_2(A_119))
      | ~ v4_orders_2(A_119)
      | ~ v5_orders_2(A_119)
      | ~ v2_orders_2(A_119)
      | ~ l1_orders_2(A_119)
      | ~ v3_orders_2(A_119) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_330,c_133])).

tff(c_520,plain,(
    ! [A_152,B_153] :
      ( m1_subset_1('#skF_1'(u1_orders_2(A_152),B_153),u1_struct_0(A_152))
      | r9_orders_1(u1_orders_2(A_152),B_153)
      | ~ r2_hidden(B_153,k3_relat_1(u1_orders_2(A_152)))
      | ~ v1_relat_1(u1_orders_2(A_152))
      | ~ v4_orders_2(A_152)
      | ~ v5_orders_2(A_152)
      | ~ v2_orders_2(A_152)
      | ~ l1_orders_2(A_152)
      | ~ v3_orders_2(A_152) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_330,c_133])).

tff(c_72,plain,(
    ! [C_49] :
      ( r9_orders_1(u1_orders_2('#skF_2'),'#skF_3')
      | r2_orders_2('#skF_2','#skF_3',C_49)
      | C_49 = '#skF_3'
      | ~ m1_subset_1(C_49,u1_struct_0('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_118,plain,(
    ! [C_49] :
      ( r2_orders_2('#skF_2','#skF_3',C_49)
      | C_49 = '#skF_3'
      | ~ m1_subset_1(C_49,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_72])).

tff(c_530,plain,(
    ! [B_153] :
      ( r2_orders_2('#skF_2','#skF_3','#skF_1'(u1_orders_2('#skF_2'),B_153))
      | '#skF_1'(u1_orders_2('#skF_2'),B_153) = '#skF_3'
      | r9_orders_1(u1_orders_2('#skF_2'),B_153)
      | ~ r2_hidden(B_153,k3_relat_1(u1_orders_2('#skF_2')))
      | ~ v1_relat_1(u1_orders_2('#skF_2'))
      | ~ v4_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v2_orders_2('#skF_2')
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_520,c_118])).

tff(c_539,plain,(
    ! [B_156] :
      ( r2_orders_2('#skF_2','#skF_3','#skF_1'(u1_orders_2('#skF_2'),B_156))
      | '#skF_1'(u1_orders_2('#skF_2'),B_156) = '#skF_3'
      | r9_orders_1(u1_orders_2('#skF_2'),B_156)
      | ~ r2_hidden(B_156,k3_relat_1(u1_orders_2('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_81,c_50,c_52,c_484,c_530])).

tff(c_10,plain,(
    ! [A_5,B_9,C_11] :
      ( r1_orders_2(A_5,B_9,C_11)
      | ~ r2_orders_2(A_5,B_9,C_11)
      | ~ m1_subset_1(C_11,u1_struct_0(A_5))
      | ~ m1_subset_1(B_9,u1_struct_0(A_5))
      | ~ l1_orders_2(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_541,plain,(
    ! [B_156] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(u1_orders_2('#skF_2'),B_156))
      | ~ m1_subset_1('#skF_1'(u1_orders_2('#skF_2'),B_156),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | '#skF_1'(u1_orders_2('#skF_2'),B_156) = '#skF_3'
      | r9_orders_1(u1_orders_2('#skF_2'),B_156)
      | ~ r2_hidden(B_156,k3_relat_1(u1_orders_2('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_539,c_10])).

tff(c_551,plain,(
    ! [B_158] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(u1_orders_2('#skF_2'),B_158))
      | ~ m1_subset_1('#skF_1'(u1_orders_2('#skF_2'),B_158),u1_struct_0('#skF_2'))
      | '#skF_1'(u1_orders_2('#skF_2'),B_158) = '#skF_3'
      | r9_orders_1(u1_orders_2('#skF_2'),B_158)
      | ~ r2_hidden(B_158,k3_relat_1(u1_orders_2('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_541])).

tff(c_555,plain,(
    ! [B_76] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(u1_orders_2('#skF_2'),B_76))
      | '#skF_1'(u1_orders_2('#skF_2'),B_76) = '#skF_3'
      | r9_orders_1(u1_orders_2('#skF_2'),B_76)
      | ~ r2_hidden(B_76,k3_relat_1(u1_orders_2('#skF_2')))
      | ~ v1_relat_1(u1_orders_2('#skF_2'))
      | ~ v4_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v2_orders_2('#skF_2')
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_341,c_551])).

tff(c_559,plain,(
    ! [B_159] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(u1_orders_2('#skF_2'),B_159))
      | '#skF_1'(u1_orders_2('#skF_2'),B_159) = '#skF_3'
      | r9_orders_1(u1_orders_2('#skF_2'),B_159)
      | ~ r2_hidden(B_159,k3_relat_1(u1_orders_2('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_81,c_50,c_52,c_484,c_555])).

tff(c_260,plain,(
    ! [B_105,C_106,A_107] :
      ( r2_hidden(k4_tarski(B_105,C_106),u1_orders_2(A_107))
      | ~ r1_orders_2(A_107,B_105,C_106)
      | ~ m1_subset_1(C_106,u1_struct_0(A_107))
      | ~ m1_subset_1(B_105,u1_struct_0(A_107))
      | ~ l1_orders_2(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_16,plain,(
    ! [B_18,A_12] :
      ( ~ r2_hidden(k4_tarski(B_18,'#skF_1'(A_12,B_18)),A_12)
      | r9_orders_1(A_12,B_18)
      | ~ r2_hidden(B_18,k3_relat_1(A_12))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_272,plain,(
    ! [A_107,B_105] :
      ( r9_orders_1(u1_orders_2(A_107),B_105)
      | ~ r2_hidden(B_105,k3_relat_1(u1_orders_2(A_107)))
      | ~ v1_relat_1(u1_orders_2(A_107))
      | ~ r1_orders_2(A_107,B_105,'#skF_1'(u1_orders_2(A_107),B_105))
      | ~ m1_subset_1('#skF_1'(u1_orders_2(A_107),B_105),u1_struct_0(A_107))
      | ~ m1_subset_1(B_105,u1_struct_0(A_107))
      | ~ l1_orders_2(A_107) ) ),
    inference(resolution,[status(thm)],[c_260,c_16])).

tff(c_562,plain,
    ( ~ v1_relat_1(u1_orders_2('#skF_2'))
    | ~ m1_subset_1('#skF_1'(u1_orders_2('#skF_2'),'#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | '#skF_1'(u1_orders_2('#skF_2'),'#skF_3') = '#skF_3'
    | r9_orders_1(u1_orders_2('#skF_2'),'#skF_3')
    | ~ r2_hidden('#skF_3',k3_relat_1(u1_orders_2('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_559,c_272])).

tff(c_565,plain,
    ( ~ m1_subset_1('#skF_1'(u1_orders_2('#skF_2'),'#skF_3'),u1_struct_0('#skF_2'))
    | '#skF_1'(u1_orders_2('#skF_2'),'#skF_3') = '#skF_3'
    | r9_orders_1(u1_orders_2('#skF_2'),'#skF_3')
    | ~ r2_hidden('#skF_3',k3_relat_1(u1_orders_2('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_484,c_562])).

tff(c_566,plain,
    ( ~ m1_subset_1('#skF_1'(u1_orders_2('#skF_2'),'#skF_3'),u1_struct_0('#skF_2'))
    | ~ r2_hidden('#skF_3',k3_relat_1(u1_orders_2('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_485,c_565])).

tff(c_567,plain,(
    ~ r2_hidden('#skF_3',k3_relat_1(u1_orders_2('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_566])).

tff(c_570,plain,
    ( ~ r2_hidden('#skF_3',u1_struct_0('#skF_2'))
    | ~ v4_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v2_orders_2('#skF_2')
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_329,c_567])).

tff(c_578,plain,(
    ~ r2_hidden('#skF_3',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_81,c_50,c_52,c_570])).

tff(c_585,plain,
    ( v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_44,c_578])).

tff(c_588,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_585])).

tff(c_32,plain,(
    ! [A_32] :
      ( ~ v1_xboole_0(u1_struct_0(A_32))
      | ~ l1_struct_0(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_591,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_588,c_32])).

tff(c_594,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_591])).

tff(c_597,plain,(
    ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_594])).

tff(c_601,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_597])).

tff(c_603,plain,(
    r2_hidden('#skF_3',k3_relat_1(u1_orders_2('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_566])).

tff(c_602,plain,(
    ~ m1_subset_1('#skF_1'(u1_orders_2('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_566])).

tff(c_668,plain,
    ( r9_orders_1(u1_orders_2('#skF_2'),'#skF_3')
    | ~ r2_hidden('#skF_3',k3_relat_1(u1_orders_2('#skF_2')))
    | ~ v1_relat_1(u1_orders_2('#skF_2'))
    | ~ v4_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v2_orders_2('#skF_2')
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_341,c_602])).

tff(c_671,plain,(
    r9_orders_1(u1_orders_2('#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_81,c_50,c_52,c_484,c_603,c_668])).

tff(c_673,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_671])).

tff(c_674,plain,(
    ~ r2_hidden('#skF_3',u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_483])).

tff(c_678,plain,
    ( v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_44,c_674])).

tff(c_681,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_678])).

tff(c_684,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_681,c_32])).

tff(c_687,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_684])).

tff(c_690,plain,(
    ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_687])).

tff(c_694,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_690])).

tff(c_695,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_696,plain,(
    r9_orders_1(u1_orders_2('#skF_2'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_58,plain,
    ( ~ r2_orders_2('#skF_2','#skF_3','#skF_4')
    | ~ r9_orders_1(u1_orders_2('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_707,plain,(
    ~ r2_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_696,c_58])).

tff(c_62,plain,
    ( m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ r9_orders_1(u1_orders_2('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_705,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_696,c_62])).

tff(c_830,plain,(
    ! [A_208,B_209,C_210] :
      ( r2_orders_2(A_208,B_209,C_210)
      | C_210 = B_209
      | ~ r1_orders_2(A_208,B_209,C_210)
      | ~ m1_subset_1(C_210,u1_struct_0(A_208))
      | ~ m1_subset_1(B_209,u1_struct_0(A_208))
      | ~ l1_orders_2(A_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_835,plain,(
    ! [B_209] :
      ( r2_orders_2('#skF_2',B_209,'#skF_4')
      | B_209 = '#skF_4'
      | ~ r1_orders_2('#skF_2',B_209,'#skF_4')
      | ~ m1_subset_1(B_209,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_705,c_830])).

tff(c_845,plain,(
    ! [B_211] :
      ( r2_orders_2('#skF_2',B_211,'#skF_4')
      | B_211 = '#skF_4'
      | ~ r1_orders_2('#skF_2',B_211,'#skF_4')
      | ~ m1_subset_1(B_211,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_835])).

tff(c_855,plain,
    ( r2_orders_2('#skF_2','#skF_3','#skF_4')
    | '#skF_3' = '#skF_4'
    | ~ r1_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_845])).

tff(c_861,plain,(
    ~ r1_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_695,c_707,c_855])).

tff(c_809,plain,(
    ! [B_204,A_205] :
      ( k3_relat_1(B_204) = A_205
      | ~ m1_subset_1(B_204,k1_zfmisc_1(k2_zfmisc_1(A_205,A_205)))
      | ~ v1_partfun1(B_204,A_205)
      | ~ v8_relat_2(B_204)
      | ~ v4_relat_2(B_204)
      | ~ v1_relat_2(B_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_945,plain,(
    ! [A_225] :
      ( k3_relat_1(u1_orders_2(A_225)) = u1_struct_0(A_225)
      | ~ v1_partfun1(u1_orders_2(A_225),u1_struct_0(A_225))
      | ~ v8_relat_2(u1_orders_2(A_225))
      | ~ v4_relat_2(u1_orders_2(A_225))
      | ~ v1_relat_2(u1_orders_2(A_225))
      | ~ l1_orders_2(A_225) ) ),
    inference(resolution,[status(thm)],[c_28,c_809])).

tff(c_950,plain,(
    ! [A_226] :
      ( k3_relat_1(u1_orders_2(A_226)) = u1_struct_0(A_226)
      | ~ v8_relat_2(u1_orders_2(A_226))
      | ~ v4_relat_2(u1_orders_2(A_226))
      | ~ v1_relat_2(u1_orders_2(A_226))
      | ~ l1_orders_2(A_226)
      | ~ v2_orders_2(A_226) ) ),
    inference(resolution,[status(thm)],[c_30,c_945])).

tff(c_955,plain,(
    ! [A_227] :
      ( k3_relat_1(u1_orders_2(A_227)) = u1_struct_0(A_227)
      | ~ v4_relat_2(u1_orders_2(A_227))
      | ~ v1_relat_2(u1_orders_2(A_227))
      | ~ l1_orders_2(A_227)
      | ~ v4_orders_2(A_227)
      | ~ v2_orders_2(A_227) ) ),
    inference(resolution,[status(thm)],[c_38,c_950])).

tff(c_960,plain,(
    ! [A_228] :
      ( k3_relat_1(u1_orders_2(A_228)) = u1_struct_0(A_228)
      | ~ v1_relat_2(u1_orders_2(A_228))
      | ~ v4_orders_2(A_228)
      | ~ l1_orders_2(A_228)
      | ~ v5_orders_2(A_228)
      | ~ v2_orders_2(A_228) ) ),
    inference(resolution,[status(thm)],[c_36,c_955])).

tff(c_964,plain,(
    ! [A_33] :
      ( k3_relat_1(u1_orders_2(A_33)) = u1_struct_0(A_33)
      | ~ v4_orders_2(A_33)
      | ~ v5_orders_2(A_33)
      | ~ v2_orders_2(A_33)
      | ~ l1_orders_2(A_33)
      | ~ v3_orders_2(A_33) ) ),
    inference(resolution,[status(thm)],[c_34,c_960])).

tff(c_719,plain,(
    ! [A_180] :
      ( m1_subset_1(u1_orders_2(A_180),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_180),u1_struct_0(A_180))))
      | ~ l1_orders_2(A_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_723,plain,(
    ! [A_180] :
      ( v1_relat_1(u1_orders_2(A_180))
      | ~ l1_orders_2(A_180) ) ),
    inference(resolution,[status(thm)],[c_719,c_4])).

tff(c_966,plain,(
    ! [A_229] :
      ( k3_relat_1(u1_orders_2(A_229)) = u1_struct_0(A_229)
      | ~ v4_orders_2(A_229)
      | ~ v5_orders_2(A_229)
      | ~ v2_orders_2(A_229)
      | ~ l1_orders_2(A_229)
      | ~ v3_orders_2(A_229) ) ),
    inference(resolution,[status(thm)],[c_34,c_960])).

tff(c_14,plain,(
    ! [B_18,A_12] :
      ( r2_hidden(B_18,k3_relat_1(A_12))
      | ~ r9_orders_1(A_12,B_18)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1002,plain,(
    ! [B_232,A_233] :
      ( r2_hidden(B_232,u1_struct_0(A_233))
      | ~ r9_orders_1(u1_orders_2(A_233),B_232)
      | ~ v1_relat_1(u1_orders_2(A_233))
      | ~ v4_orders_2(A_233)
      | ~ v5_orders_2(A_233)
      | ~ v2_orders_2(A_233)
      | ~ l1_orders_2(A_233)
      | ~ v3_orders_2(A_233) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_966,c_14])).

tff(c_1005,plain,
    ( r2_hidden('#skF_3',u1_struct_0('#skF_2'))
    | ~ v1_relat_1(u1_orders_2('#skF_2'))
    | ~ v4_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v2_orders_2('#skF_2')
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_696,c_1002])).

tff(c_1008,plain,
    ( r2_hidden('#skF_3',u1_struct_0('#skF_2'))
    | ~ v1_relat_1(u1_orders_2('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_81,c_50,c_52,c_1005])).

tff(c_1009,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1008])).

tff(c_1016,plain,(
    ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_723,c_1009])).

tff(c_1020,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1016])).

tff(c_1022,plain,(
    v1_relat_1(u1_orders_2('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1008])).

tff(c_983,plain,(
    ! [A_229,B_18] :
      ( '#skF_1'(u1_orders_2(A_229),B_18) != B_18
      | r9_orders_1(u1_orders_2(A_229),B_18)
      | ~ r2_hidden(B_18,u1_struct_0(A_229))
      | ~ v1_relat_1(u1_orders_2(A_229))
      | ~ v4_orders_2(A_229)
      | ~ v5_orders_2(A_229)
      | ~ v2_orders_2(A_229)
      | ~ l1_orders_2(A_229)
      | ~ v3_orders_2(A_229) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_966,c_18])).

tff(c_12,plain,(
    ! [B_18,C_21,A_12] :
      ( r2_hidden(k4_tarski(B_18,C_21),A_12)
      | C_21 = B_18
      | ~ r2_hidden(C_21,k3_relat_1(A_12))
      | ~ r9_orders_1(A_12,B_18)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_925,plain,(
    ! [A_219,B_220,C_221] :
      ( r1_orders_2(A_219,B_220,C_221)
      | ~ r2_hidden(k4_tarski(B_220,C_221),u1_orders_2(A_219))
      | ~ m1_subset_1(C_221,u1_struct_0(A_219))
      | ~ m1_subset_1(B_220,u1_struct_0(A_219))
      | ~ l1_orders_2(A_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1103,plain,(
    ! [A_250,B_251,C_252] :
      ( r1_orders_2(A_250,B_251,C_252)
      | ~ m1_subset_1(C_252,u1_struct_0(A_250))
      | ~ m1_subset_1(B_251,u1_struct_0(A_250))
      | ~ l1_orders_2(A_250)
      | C_252 = B_251
      | ~ r2_hidden(C_252,k3_relat_1(u1_orders_2(A_250)))
      | ~ r9_orders_1(u1_orders_2(A_250),B_251)
      | ~ v1_relat_1(u1_orders_2(A_250)) ) ),
    inference(resolution,[status(thm)],[c_12,c_925])).

tff(c_1136,plain,(
    ! [A_255,B_256,B_257] :
      ( r1_orders_2(A_255,B_256,B_257)
      | ~ m1_subset_1(B_257,u1_struct_0(A_255))
      | ~ m1_subset_1(B_256,u1_struct_0(A_255))
      | ~ l1_orders_2(A_255)
      | B_257 = B_256
      | ~ r9_orders_1(u1_orders_2(A_255),B_256)
      | ~ r9_orders_1(u1_orders_2(A_255),B_257)
      | ~ v1_relat_1(u1_orders_2(A_255)) ) ),
    inference(resolution,[status(thm)],[c_14,c_1103])).

tff(c_1143,plain,(
    ! [B_257] :
      ( r1_orders_2('#skF_2','#skF_3',B_257)
      | ~ m1_subset_1(B_257,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | B_257 = '#skF_3'
      | ~ r9_orders_1(u1_orders_2('#skF_2'),B_257)
      | ~ v1_relat_1(u1_orders_2('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_696,c_1136])).

tff(c_1149,plain,(
    ! [B_258] :
      ( r1_orders_2('#skF_2','#skF_3',B_258)
      | ~ m1_subset_1(B_258,u1_struct_0('#skF_2'))
      | B_258 = '#skF_3'
      | ~ r9_orders_1(u1_orders_2('#skF_2'),B_258) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1022,c_48,c_46,c_1143])).

tff(c_1153,plain,(
    ! [B_18] :
      ( r1_orders_2('#skF_2','#skF_3',B_18)
      | ~ m1_subset_1(B_18,u1_struct_0('#skF_2'))
      | B_18 = '#skF_3'
      | '#skF_1'(u1_orders_2('#skF_2'),B_18) != B_18
      | ~ r2_hidden(B_18,u1_struct_0('#skF_2'))
      | ~ v1_relat_1(u1_orders_2('#skF_2'))
      | ~ v4_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v2_orders_2('#skF_2')
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_983,c_1149])).

tff(c_1171,plain,(
    ! [B_259] :
      ( r1_orders_2('#skF_2','#skF_3',B_259)
      | ~ m1_subset_1(B_259,u1_struct_0('#skF_2'))
      | B_259 = '#skF_3'
      | '#skF_1'(u1_orders_2('#skF_2'),B_259) != B_259
      | ~ r2_hidden(B_259,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_81,c_50,c_52,c_1022,c_1153])).

tff(c_1188,plain,(
    ! [A_40] :
      ( r1_orders_2('#skF_2','#skF_3',A_40)
      | A_40 = '#skF_3'
      | '#skF_1'(u1_orders_2('#skF_2'),A_40) != A_40
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ m1_subset_1(A_40,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_44,c_1171])).

tff(c_1189,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1188])).

tff(c_1192,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_1189,c_32])).

tff(c_1195,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1192])).

tff(c_1217,plain,(
    ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_1195])).

tff(c_1221,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1217])).

tff(c_1223,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1188])).

tff(c_1421,plain,(
    ! [A_295,B_296,A_297] :
      ( r1_orders_2(A_295,B_296,A_297)
      | ~ m1_subset_1(A_297,u1_struct_0(A_295))
      | ~ m1_subset_1(B_296,u1_struct_0(A_295))
      | ~ l1_orders_2(A_295)
      | B_296 = A_297
      | ~ r9_orders_1(u1_orders_2(A_295),B_296)
      | ~ v1_relat_1(u1_orders_2(A_295))
      | v1_xboole_0(k3_relat_1(u1_orders_2(A_295)))
      | ~ m1_subset_1(A_297,k3_relat_1(u1_orders_2(A_295))) ) ),
    inference(resolution,[status(thm)],[c_44,c_1103])).

tff(c_1430,plain,(
    ! [A_297] :
      ( r1_orders_2('#skF_2','#skF_3',A_297)
      | ~ m1_subset_1(A_297,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | A_297 = '#skF_3'
      | ~ v1_relat_1(u1_orders_2('#skF_2'))
      | v1_xboole_0(k3_relat_1(u1_orders_2('#skF_2')))
      | ~ m1_subset_1(A_297,k3_relat_1(u1_orders_2('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_696,c_1421])).

tff(c_1436,plain,(
    ! [A_297] :
      ( r1_orders_2('#skF_2','#skF_3',A_297)
      | ~ m1_subset_1(A_297,u1_struct_0('#skF_2'))
      | A_297 = '#skF_3'
      | v1_xboole_0(k3_relat_1(u1_orders_2('#skF_2')))
      | ~ m1_subset_1(A_297,k3_relat_1(u1_orders_2('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1022,c_48,c_46,c_1430])).

tff(c_1437,plain,(
    v1_xboole_0(k3_relat_1(u1_orders_2('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1436])).

tff(c_1440,plain,
    ( v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ v4_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v2_orders_2('#skF_2')
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_964,c_1437])).

tff(c_1442,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_81,c_50,c_52,c_1440])).

tff(c_1444,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1223,c_1442])).

tff(c_1458,plain,(
    ! [A_298] :
      ( r1_orders_2('#skF_2','#skF_3',A_298)
      | ~ m1_subset_1(A_298,u1_struct_0('#skF_2'))
      | A_298 = '#skF_3'
      | ~ m1_subset_1(A_298,k3_relat_1(u1_orders_2('#skF_2'))) ) ),
    inference(splitRight,[status(thm)],[c_1436])).

tff(c_1469,plain,(
    ! [A_298] :
      ( r1_orders_2('#skF_2','#skF_3',A_298)
      | ~ m1_subset_1(A_298,u1_struct_0('#skF_2'))
      | A_298 = '#skF_3'
      | ~ m1_subset_1(A_298,u1_struct_0('#skF_2'))
      | ~ v4_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v2_orders_2('#skF_2')
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_964,c_1458])).

tff(c_1498,plain,(
    ! [A_299] :
      ( r1_orders_2('#skF_2','#skF_3',A_299)
      | A_299 = '#skF_3'
      | ~ m1_subset_1(A_299,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_81,c_50,c_52,c_1469])).

tff(c_1521,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_705,c_1498])).

tff(c_1535,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_695,c_861,c_1521])).

%------------------------------------------------------------------------------
