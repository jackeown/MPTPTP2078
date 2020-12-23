%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:05 EST 2020

% Result     : Theorem 7.40s
% Output     : CNFRefutation 7.57s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 241 expanded)
%              Number of leaves         :   28 (  94 expanded)
%              Depth                    :   14
%              Number of atoms          :  303 ( 860 expanded)
%              Number of equality atoms :   16 ( 134 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k6_setfam_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_137,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ( v4_pre_topc(B,A)
               => k2_pre_topc(A,B) = B )
              & ( ( v2_pre_topc(A)
                  & k2_pre_topc(A,B) = B )
               => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_114,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ? [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
              & ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                 => ( r2_hidden(D,C)
                  <=> ( v4_pre_topc(D,A)
                      & r1_tarski(B,D) ) ) )
              & k2_pre_topc(A,B) = k6_setfam_1(u1_struct_0(A),C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_pre_topc)).

tff(f_74,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r2_hidden(C,B)
                 => v4_pre_topc(C,A) ) )
           => v4_pre_topc(k6_setfam_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_pre_topc)).

tff(f_121,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                 => r2_hidden(D,C) ) )
           => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_93,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( r2_hidden(C,u1_struct_0(A))
             => ( r2_hidden(C,k2_pre_topc(A,B))
              <=> ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                   => ( ( v4_pre_topc(D,A)
                        & r1_tarski(B,D) )
                     => r2_hidden(C,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_pre_topc)).

tff(c_60,plain,
    ( v4_pre_topc('#skF_6','#skF_5')
    | v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_63,plain,(
    v2_pre_topc('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_48,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_46,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_36,plain,(
    ! [A_44,B_52] :
      ( m1_subset_1('#skF_4'(A_44,B_52),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_44))))
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_pre_topc(A_44)
      | ~ v2_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_56,plain,
    ( v4_pre_topc('#skF_6','#skF_5')
    | k2_pre_topc('#skF_5','#skF_6') = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_65,plain,(
    k2_pre_topc('#skF_5','#skF_6') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_50,plain,
    ( k2_pre_topc('#skF_5','#skF_6') != '#skF_6'
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_71,plain,(
    ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_50])).

tff(c_126,plain,(
    ! [A_85,B_86] :
      ( k6_setfam_1(u1_struct_0(A_85),'#skF_4'(A_85,B_86)) = k2_pre_topc(A_85,B_86)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85)
      | ~ v2_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_133,plain,
    ( k6_setfam_1(u1_struct_0('#skF_5'),'#skF_4'('#skF_5','#skF_6')) = k2_pre_topc('#skF_5','#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_126])).

tff(c_138,plain,(
    k6_setfam_1(u1_struct_0('#skF_5'),'#skF_4'('#skF_5','#skF_6')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_48,c_65,c_133])).

tff(c_22,plain,(
    ! [A_16,B_20] :
      ( m1_subset_1('#skF_2'(A_16,B_20),k1_zfmisc_1(u1_struct_0(A_16)))
      | v4_pre_topc(k6_setfam_1(u1_struct_0(A_16),B_20),A_16)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_16))))
      | ~ l1_pre_topc(A_16)
      | ~ v2_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_143,plain,(
    ! [A_87,B_88] :
      ( ~ v4_pre_topc('#skF_2'(A_87,B_88),A_87)
      | v4_pre_topc(k6_setfam_1(u1_struct_0(A_87),B_88),A_87)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_87))))
      | ~ l1_pre_topc(A_87)
      | ~ v2_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_291,plain,(
    ! [A_123,B_124] :
      ( ~ v4_pre_topc('#skF_2'(A_123,'#skF_4'(A_123,B_124)),A_123)
      | v4_pre_topc(k6_setfam_1(u1_struct_0(A_123),'#skF_4'(A_123,B_124)),A_123)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_pre_topc(A_123)
      | ~ v2_pre_topc(A_123) ) ),
    inference(resolution,[status(thm)],[c_36,c_143])).

tff(c_297,plain,
    ( ~ v4_pre_topc('#skF_2'('#skF_5','#skF_4'('#skF_5','#skF_6')),'#skF_5')
    | v4_pre_topc('#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_291])).

tff(c_299,plain,
    ( ~ v4_pre_topc('#skF_2'('#skF_5','#skF_4'('#skF_5','#skF_6')),'#skF_5')
    | v4_pre_topc('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_48,c_46,c_297])).

tff(c_300,plain,(
    ~ v4_pre_topc('#skF_2'('#skF_5','#skF_4'('#skF_5','#skF_6')),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_299])).

tff(c_151,plain,(
    ! [A_89,B_90] :
      ( r2_hidden('#skF_2'(A_89,B_90),B_90)
      | v4_pre_topc(k6_setfam_1(u1_struct_0(A_89),B_90),A_89)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_89))))
      | ~ l1_pre_topc(A_89)
      | ~ v2_pre_topc(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_415,plain,(
    ! [A_163,B_164] :
      ( r2_hidden('#skF_2'(A_163,'#skF_4'(A_163,B_164)),'#skF_4'(A_163,B_164))
      | v4_pre_topc(k6_setfam_1(u1_struct_0(A_163),'#skF_4'(A_163,B_164)),A_163)
      | ~ m1_subset_1(B_164,k1_zfmisc_1(u1_struct_0(A_163)))
      | ~ l1_pre_topc(A_163)
      | ~ v2_pre_topc(A_163) ) ),
    inference(resolution,[status(thm)],[c_36,c_151])).

tff(c_425,plain,
    ( r2_hidden('#skF_2'('#skF_5','#skF_4'('#skF_5','#skF_6')),'#skF_4'('#skF_5','#skF_6'))
    | v4_pre_topc('#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_415])).

tff(c_430,plain,
    ( r2_hidden('#skF_2'('#skF_5','#skF_4'('#skF_5','#skF_6')),'#skF_4'('#skF_5','#skF_6'))
    | v4_pre_topc('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_48,c_46,c_425])).

tff(c_431,plain,(
    r2_hidden('#skF_2'('#skF_5','#skF_4'('#skF_5','#skF_6')),'#skF_4'('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_430])).

tff(c_42,plain,(
    ! [D_57,A_44,B_52] :
      ( v4_pre_topc(D_57,A_44)
      | ~ r2_hidden(D_57,'#skF_4'(A_44,B_52))
      | ~ m1_subset_1(D_57,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_pre_topc(A_44)
      | ~ v2_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_433,plain,
    ( v4_pre_topc('#skF_2'('#skF_5','#skF_4'('#skF_5','#skF_6')),'#skF_5')
    | ~ m1_subset_1('#skF_2'('#skF_5','#skF_4'('#skF_5','#skF_6')),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_431,c_42])).

tff(c_440,plain,
    ( v4_pre_topc('#skF_2'('#skF_5','#skF_4'('#skF_5','#skF_6')),'#skF_5')
    | ~ m1_subset_1('#skF_2'('#skF_5','#skF_4'('#skF_5','#skF_6')),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_48,c_46,c_433])).

tff(c_441,plain,(
    ~ m1_subset_1('#skF_2'('#skF_5','#skF_4'('#skF_5','#skF_6')),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_300,c_440])).

tff(c_448,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0('#skF_5'),'#skF_4'('#skF_5','#skF_6')),'#skF_5')
    | ~ m1_subset_1('#skF_4'('#skF_5','#skF_6'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5'))))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_441])).

tff(c_451,plain,
    ( v4_pre_topc('#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_4'('#skF_5','#skF_6'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_48,c_138,c_448])).

tff(c_452,plain,(
    ~ m1_subset_1('#skF_4'('#skF_5','#skF_6'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5')))) ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_451])).

tff(c_455,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_452])).

tff(c_459,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_48,c_46,c_455])).

tff(c_461,plain,(
    k2_pre_topc('#skF_5','#skF_6') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_472,plain,(
    ! [B_170,A_171] :
      ( r1_tarski(B_170,k2_pre_topc(A_171,B_170))
      | ~ m1_subset_1(B_170,k1_zfmisc_1(u1_struct_0(A_171)))
      | ~ l1_pre_topc(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_474,plain,
    ( r1_tarski('#skF_6',k2_pre_topc('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_472])).

tff(c_477,plain,(
    r1_tarski('#skF_6',k2_pre_topc('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_474])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_479,plain,
    ( k2_pre_topc('#skF_5','#skF_6') = '#skF_6'
    | ~ r1_tarski(k2_pre_topc('#skF_5','#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_477,c_2])).

tff(c_482,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_5','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_461,c_479])).

tff(c_460,plain,(
    v4_pre_topc('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_16,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(k2_pre_topc(A_14,B_15),k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_493,plain,(
    ! [A_181,B_182,C_183] :
      ( r2_hidden('#skF_1'(A_181,B_182,C_183),B_182)
      | r1_tarski(B_182,C_183)
      | ~ m1_subset_1(C_183,k1_zfmisc_1(A_181))
      | ~ m1_subset_1(B_182,k1_zfmisc_1(A_181)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_8,plain,(
    ! [C_6,A_3,B_4] :
      ( r2_hidden(C_6,A_3)
      | ~ r2_hidden(C_6,B_4)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_502,plain,(
    ! [A_181,B_182,C_183,A_3] :
      ( r2_hidden('#skF_1'(A_181,B_182,C_183),A_3)
      | ~ m1_subset_1(B_182,k1_zfmisc_1(A_3))
      | r1_tarski(B_182,C_183)
      | ~ m1_subset_1(C_183,k1_zfmisc_1(A_181))
      | ~ m1_subset_1(B_182,k1_zfmisc_1(A_181)) ) ),
    inference(resolution,[status(thm)],[c_493,c_8])).

tff(c_12,plain,(
    ! [A_7,B_8,C_12] :
      ( r2_hidden('#skF_1'(A_7,B_8,C_12),B_8)
      | r1_tarski(B_8,C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(A_7))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_826,plain,(
    ! [C_250,D_251,B_252,A_253] :
      ( r2_hidden(C_250,D_251)
      | ~ r1_tarski(B_252,D_251)
      | ~ v4_pre_topc(D_251,A_253)
      | ~ m1_subset_1(D_251,k1_zfmisc_1(u1_struct_0(A_253)))
      | ~ r2_hidden(C_250,k2_pre_topc(A_253,B_252))
      | ~ r2_hidden(C_250,u1_struct_0(A_253))
      | ~ m1_subset_1(B_252,k1_zfmisc_1(u1_struct_0(A_253)))
      | ~ l1_pre_topc(A_253) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_836,plain,(
    ! [C_254,B_255,A_256] :
      ( r2_hidden(C_254,B_255)
      | ~ v4_pre_topc(B_255,A_256)
      | ~ r2_hidden(C_254,k2_pre_topc(A_256,B_255))
      | ~ r2_hidden(C_254,u1_struct_0(A_256))
      | ~ m1_subset_1(B_255,k1_zfmisc_1(u1_struct_0(A_256)))
      | ~ l1_pre_topc(A_256) ) ),
    inference(resolution,[status(thm)],[c_6,c_826])).

tff(c_1618,plain,(
    ! [A_548,A_549,B_550,C_551] :
      ( r2_hidden('#skF_1'(A_548,k2_pre_topc(A_549,B_550),C_551),B_550)
      | ~ v4_pre_topc(B_550,A_549)
      | ~ r2_hidden('#skF_1'(A_548,k2_pre_topc(A_549,B_550),C_551),u1_struct_0(A_549))
      | ~ m1_subset_1(B_550,k1_zfmisc_1(u1_struct_0(A_549)))
      | ~ l1_pre_topc(A_549)
      | r1_tarski(k2_pre_topc(A_549,B_550),C_551)
      | ~ m1_subset_1(C_551,k1_zfmisc_1(A_548))
      | ~ m1_subset_1(k2_pre_topc(A_549,B_550),k1_zfmisc_1(A_548)) ) ),
    inference(resolution,[status(thm)],[c_12,c_836])).

tff(c_1696,plain,(
    ! [A_561,A_562,B_563,C_564] :
      ( r2_hidden('#skF_1'(A_561,k2_pre_topc(A_562,B_563),C_564),B_563)
      | ~ v4_pre_topc(B_563,A_562)
      | ~ m1_subset_1(B_563,k1_zfmisc_1(u1_struct_0(A_562)))
      | ~ l1_pre_topc(A_562)
      | ~ m1_subset_1(k2_pre_topc(A_562,B_563),k1_zfmisc_1(u1_struct_0(A_562)))
      | r1_tarski(k2_pre_topc(A_562,B_563),C_564)
      | ~ m1_subset_1(C_564,k1_zfmisc_1(A_561))
      | ~ m1_subset_1(k2_pre_topc(A_562,B_563),k1_zfmisc_1(A_561)) ) ),
    inference(resolution,[status(thm)],[c_502,c_1618])).

tff(c_1700,plain,(
    ! [A_565,A_566,B_567,C_568] :
      ( r2_hidden('#skF_1'(A_565,k2_pre_topc(A_566,B_567),C_568),B_567)
      | ~ v4_pre_topc(B_567,A_566)
      | r1_tarski(k2_pre_topc(A_566,B_567),C_568)
      | ~ m1_subset_1(C_568,k1_zfmisc_1(A_565))
      | ~ m1_subset_1(k2_pre_topc(A_566,B_567),k1_zfmisc_1(A_565))
      | ~ m1_subset_1(B_567,k1_zfmisc_1(u1_struct_0(A_566)))
      | ~ l1_pre_topc(A_566) ) ),
    inference(resolution,[status(thm)],[c_16,c_1696])).

tff(c_10,plain,(
    ! [A_7,B_8,C_12] :
      ( ~ r2_hidden('#skF_1'(A_7,B_8,C_12),C_12)
      | r1_tarski(B_8,C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(A_7))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1735,plain,(
    ! [B_569,A_570,A_571] :
      ( ~ v4_pre_topc(B_569,A_570)
      | r1_tarski(k2_pre_topc(A_570,B_569),B_569)
      | ~ m1_subset_1(B_569,k1_zfmisc_1(A_571))
      | ~ m1_subset_1(k2_pre_topc(A_570,B_569),k1_zfmisc_1(A_571))
      | ~ m1_subset_1(B_569,k1_zfmisc_1(u1_struct_0(A_570)))
      | ~ l1_pre_topc(A_570) ) ),
    inference(resolution,[status(thm)],[c_1700,c_10])).

tff(c_1739,plain,(
    ! [B_572,A_573] :
      ( ~ v4_pre_topc(B_572,A_573)
      | r1_tarski(k2_pre_topc(A_573,B_572),B_572)
      | ~ m1_subset_1(B_572,k1_zfmisc_1(u1_struct_0(A_573)))
      | ~ l1_pre_topc(A_573) ) ),
    inference(resolution,[status(thm)],[c_16,c_1735])).

tff(c_1750,plain,
    ( ~ v4_pre_topc('#skF_6','#skF_5')
    | r1_tarski(k2_pre_topc('#skF_5','#skF_6'),'#skF_6')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_1739])).

tff(c_1757,plain,(
    r1_tarski(k2_pre_topc('#skF_5','#skF_6'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_460,c_1750])).

tff(c_1759,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_482,c_1757])).

tff(c_1761,plain,(
    ~ v2_pre_topc('#skF_5') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_58,plain,
    ( k2_pre_topc('#skF_5','#skF_6') != '#skF_6'
    | v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_1762,plain,(
    k2_pre_topc('#skF_5','#skF_6') != '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_1761,c_58])).

tff(c_1775,plain,(
    ! [B_579,A_580] :
      ( r1_tarski(B_579,k2_pre_topc(A_580,B_579))
      | ~ m1_subset_1(B_579,k1_zfmisc_1(u1_struct_0(A_580)))
      | ~ l1_pre_topc(A_580) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1777,plain,
    ( r1_tarski('#skF_6',k2_pre_topc('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_1775])).

tff(c_1780,plain,(
    r1_tarski('#skF_6',k2_pre_topc('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1777])).

tff(c_1782,plain,
    ( k2_pre_topc('#skF_5','#skF_6') = '#skF_6'
    | ~ r1_tarski(k2_pre_topc('#skF_5','#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_1780,c_2])).

tff(c_1785,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_5','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_1762,c_1782])).

tff(c_1760,plain,(
    v4_pre_topc('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_1795,plain,(
    ! [A_588,B_589,C_590] :
      ( r2_hidden('#skF_1'(A_588,B_589,C_590),B_589)
      | r1_tarski(B_589,C_590)
      | ~ m1_subset_1(C_590,k1_zfmisc_1(A_588))
      | ~ m1_subset_1(B_589,k1_zfmisc_1(A_588)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1804,plain,(
    ! [A_588,B_589,C_590,A_3] :
      ( r2_hidden('#skF_1'(A_588,B_589,C_590),A_3)
      | ~ m1_subset_1(B_589,k1_zfmisc_1(A_3))
      | r1_tarski(B_589,C_590)
      | ~ m1_subset_1(C_590,k1_zfmisc_1(A_588))
      | ~ m1_subset_1(B_589,k1_zfmisc_1(A_588)) ) ),
    inference(resolution,[status(thm)],[c_1795,c_8])).

tff(c_2072,plain,(
    ! [C_677,D_678,B_679,A_680] :
      ( r2_hidden(C_677,D_678)
      | ~ r1_tarski(B_679,D_678)
      | ~ v4_pre_topc(D_678,A_680)
      | ~ m1_subset_1(D_678,k1_zfmisc_1(u1_struct_0(A_680)))
      | ~ r2_hidden(C_677,k2_pre_topc(A_680,B_679))
      | ~ r2_hidden(C_677,u1_struct_0(A_680))
      | ~ m1_subset_1(B_679,k1_zfmisc_1(u1_struct_0(A_680)))
      | ~ l1_pre_topc(A_680) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2091,plain,(
    ! [C_681,B_682,A_683] :
      ( r2_hidden(C_681,B_682)
      | ~ v4_pre_topc(B_682,A_683)
      | ~ r2_hidden(C_681,k2_pre_topc(A_683,B_682))
      | ~ r2_hidden(C_681,u1_struct_0(A_683))
      | ~ m1_subset_1(B_682,k1_zfmisc_1(u1_struct_0(A_683)))
      | ~ l1_pre_topc(A_683) ) ),
    inference(resolution,[status(thm)],[c_6,c_2072])).

tff(c_2692,plain,(
    ! [A_935,A_936,B_937,C_938] :
      ( r2_hidden('#skF_1'(A_935,k2_pre_topc(A_936,B_937),C_938),B_937)
      | ~ v4_pre_topc(B_937,A_936)
      | ~ r2_hidden('#skF_1'(A_935,k2_pre_topc(A_936,B_937),C_938),u1_struct_0(A_936))
      | ~ m1_subset_1(B_937,k1_zfmisc_1(u1_struct_0(A_936)))
      | ~ l1_pre_topc(A_936)
      | r1_tarski(k2_pre_topc(A_936,B_937),C_938)
      | ~ m1_subset_1(C_938,k1_zfmisc_1(A_935))
      | ~ m1_subset_1(k2_pre_topc(A_936,B_937),k1_zfmisc_1(A_935)) ) ),
    inference(resolution,[status(thm)],[c_12,c_2091])).

tff(c_2745,plain,(
    ! [A_944,A_945,B_946,C_947] :
      ( r2_hidden('#skF_1'(A_944,k2_pre_topc(A_945,B_946),C_947),B_946)
      | ~ v4_pre_topc(B_946,A_945)
      | ~ m1_subset_1(B_946,k1_zfmisc_1(u1_struct_0(A_945)))
      | ~ l1_pre_topc(A_945)
      | ~ m1_subset_1(k2_pre_topc(A_945,B_946),k1_zfmisc_1(u1_struct_0(A_945)))
      | r1_tarski(k2_pre_topc(A_945,B_946),C_947)
      | ~ m1_subset_1(C_947,k1_zfmisc_1(A_944))
      | ~ m1_subset_1(k2_pre_topc(A_945,B_946),k1_zfmisc_1(A_944)) ) ),
    inference(resolution,[status(thm)],[c_1804,c_2692])).

tff(c_2749,plain,(
    ! [A_948,A_949,B_950,C_951] :
      ( r2_hidden('#skF_1'(A_948,k2_pre_topc(A_949,B_950),C_951),B_950)
      | ~ v4_pre_topc(B_950,A_949)
      | r1_tarski(k2_pre_topc(A_949,B_950),C_951)
      | ~ m1_subset_1(C_951,k1_zfmisc_1(A_948))
      | ~ m1_subset_1(k2_pre_topc(A_949,B_950),k1_zfmisc_1(A_948))
      | ~ m1_subset_1(B_950,k1_zfmisc_1(u1_struct_0(A_949)))
      | ~ l1_pre_topc(A_949) ) ),
    inference(resolution,[status(thm)],[c_16,c_2745])).

tff(c_2784,plain,(
    ! [B_952,A_953,A_954] :
      ( ~ v4_pre_topc(B_952,A_953)
      | r1_tarski(k2_pre_topc(A_953,B_952),B_952)
      | ~ m1_subset_1(B_952,k1_zfmisc_1(A_954))
      | ~ m1_subset_1(k2_pre_topc(A_953,B_952),k1_zfmisc_1(A_954))
      | ~ m1_subset_1(B_952,k1_zfmisc_1(u1_struct_0(A_953)))
      | ~ l1_pre_topc(A_953) ) ),
    inference(resolution,[status(thm)],[c_2749,c_10])).

tff(c_2788,plain,(
    ! [B_955,A_956] :
      ( ~ v4_pre_topc(B_955,A_956)
      | r1_tarski(k2_pre_topc(A_956,B_955),B_955)
      | ~ m1_subset_1(B_955,k1_zfmisc_1(u1_struct_0(A_956)))
      | ~ l1_pre_topc(A_956) ) ),
    inference(resolution,[status(thm)],[c_16,c_2784])).

tff(c_2799,plain,
    ( ~ v4_pre_topc('#skF_6','#skF_5')
    | r1_tarski(k2_pre_topc('#skF_5','#skF_6'),'#skF_6')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_2788])).

tff(c_2806,plain,(
    r1_tarski(k2_pre_topc('#skF_5','#skF_6'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1760,c_2799])).

tff(c_2808,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1785,c_2806])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:54:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.40/2.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.40/2.56  
% 7.40/2.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.40/2.56  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k6_setfam_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 7.40/2.56  
% 7.40/2.56  %Foreground sorts:
% 7.40/2.56  
% 7.40/2.56  
% 7.40/2.56  %Background operators:
% 7.40/2.56  
% 7.40/2.56  
% 7.40/2.56  %Foreground operators:
% 7.40/2.56  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.40/2.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.40/2.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.40/2.56  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.40/2.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.40/2.56  tff('#skF_5', type, '#skF_5': $i).
% 7.40/2.56  tff('#skF_6', type, '#skF_6': $i).
% 7.40/2.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.40/2.56  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 7.40/2.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.40/2.56  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 7.40/2.56  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.40/2.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.40/2.56  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.40/2.56  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.40/2.56  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.40/2.56  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 7.40/2.56  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.40/2.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.40/2.56  
% 7.57/2.58  tff(f_137, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 7.57/2.58  tff(f_114, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (?[C]: ((m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> (v4_pre_topc(D, A) & r1_tarski(B, D)))))) & (k2_pre_topc(A, B) = k6_setfam_1(u1_struct_0(A), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_pre_topc)).
% 7.57/2.58  tff(f_74, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ((![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, B) => v4_pre_topc(C, A)))) => v4_pre_topc(k6_setfam_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_pre_topc)).
% 7.57/2.58  tff(f_121, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 7.57/2.58  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.57/2.58  tff(f_58, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 7.57/2.58  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_subset_1)).
% 7.57/2.58  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 7.57/2.58  tff(f_93, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (r2_hidden(C, u1_struct_0(A)) => (r2_hidden(C, k2_pre_topc(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(D, A) & r1_tarski(B, D)) => r2_hidden(C, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_pre_topc)).
% 7.57/2.58  tff(c_60, plain, (v4_pre_topc('#skF_6', '#skF_5') | v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_137])).
% 7.57/2.58  tff(c_63, plain, (v2_pre_topc('#skF_5')), inference(splitLeft, [status(thm)], [c_60])).
% 7.57/2.58  tff(c_48, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_137])).
% 7.57/2.58  tff(c_46, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_137])).
% 7.57/2.58  tff(c_36, plain, (![A_44, B_52]: (m1_subset_1('#skF_4'(A_44, B_52), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_44)))) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_44))) | ~l1_pre_topc(A_44) | ~v2_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_114])).
% 7.57/2.58  tff(c_56, plain, (v4_pre_topc('#skF_6', '#skF_5') | k2_pre_topc('#skF_5', '#skF_6')='#skF_6'), inference(cnfTransformation, [status(thm)], [f_137])).
% 7.57/2.58  tff(c_65, plain, (k2_pre_topc('#skF_5', '#skF_6')='#skF_6'), inference(splitLeft, [status(thm)], [c_56])).
% 7.57/2.58  tff(c_50, plain, (k2_pre_topc('#skF_5', '#skF_6')!='#skF_6' | ~v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_137])).
% 7.57/2.58  tff(c_71, plain, (~v4_pre_topc('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_50])).
% 7.57/2.58  tff(c_126, plain, (![A_85, B_86]: (k6_setfam_1(u1_struct_0(A_85), '#skF_4'(A_85, B_86))=k2_pre_topc(A_85, B_86) | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85) | ~v2_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_114])).
% 7.57/2.58  tff(c_133, plain, (k6_setfam_1(u1_struct_0('#skF_5'), '#skF_4'('#skF_5', '#skF_6'))=k2_pre_topc('#skF_5', '#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_46, c_126])).
% 7.57/2.58  tff(c_138, plain, (k6_setfam_1(u1_struct_0('#skF_5'), '#skF_4'('#skF_5', '#skF_6'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_63, c_48, c_65, c_133])).
% 7.57/2.58  tff(c_22, plain, (![A_16, B_20]: (m1_subset_1('#skF_2'(A_16, B_20), k1_zfmisc_1(u1_struct_0(A_16))) | v4_pre_topc(k6_setfam_1(u1_struct_0(A_16), B_20), A_16) | ~m1_subset_1(B_20, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_16)))) | ~l1_pre_topc(A_16) | ~v2_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.57/2.58  tff(c_143, plain, (![A_87, B_88]: (~v4_pre_topc('#skF_2'(A_87, B_88), A_87) | v4_pre_topc(k6_setfam_1(u1_struct_0(A_87), B_88), A_87) | ~m1_subset_1(B_88, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_87)))) | ~l1_pre_topc(A_87) | ~v2_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.57/2.58  tff(c_291, plain, (![A_123, B_124]: (~v4_pre_topc('#skF_2'(A_123, '#skF_4'(A_123, B_124)), A_123) | v4_pre_topc(k6_setfam_1(u1_struct_0(A_123), '#skF_4'(A_123, B_124)), A_123) | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0(A_123))) | ~l1_pre_topc(A_123) | ~v2_pre_topc(A_123))), inference(resolution, [status(thm)], [c_36, c_143])).
% 7.57/2.58  tff(c_297, plain, (~v4_pre_topc('#skF_2'('#skF_5', '#skF_4'('#skF_5', '#skF_6')), '#skF_5') | v4_pre_topc('#skF_6', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_138, c_291])).
% 7.57/2.58  tff(c_299, plain, (~v4_pre_topc('#skF_2'('#skF_5', '#skF_4'('#skF_5', '#skF_6')), '#skF_5') | v4_pre_topc('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_48, c_46, c_297])).
% 7.57/2.58  tff(c_300, plain, (~v4_pre_topc('#skF_2'('#skF_5', '#skF_4'('#skF_5', '#skF_6')), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_71, c_299])).
% 7.57/2.58  tff(c_151, plain, (![A_89, B_90]: (r2_hidden('#skF_2'(A_89, B_90), B_90) | v4_pre_topc(k6_setfam_1(u1_struct_0(A_89), B_90), A_89) | ~m1_subset_1(B_90, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_89)))) | ~l1_pre_topc(A_89) | ~v2_pre_topc(A_89))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.57/2.58  tff(c_415, plain, (![A_163, B_164]: (r2_hidden('#skF_2'(A_163, '#skF_4'(A_163, B_164)), '#skF_4'(A_163, B_164)) | v4_pre_topc(k6_setfam_1(u1_struct_0(A_163), '#skF_4'(A_163, B_164)), A_163) | ~m1_subset_1(B_164, k1_zfmisc_1(u1_struct_0(A_163))) | ~l1_pre_topc(A_163) | ~v2_pre_topc(A_163))), inference(resolution, [status(thm)], [c_36, c_151])).
% 7.57/2.58  tff(c_425, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_4'('#skF_5', '#skF_6')), '#skF_4'('#skF_5', '#skF_6')) | v4_pre_topc('#skF_6', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_138, c_415])).
% 7.57/2.58  tff(c_430, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_4'('#skF_5', '#skF_6')), '#skF_4'('#skF_5', '#skF_6')) | v4_pre_topc('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_48, c_46, c_425])).
% 7.57/2.58  tff(c_431, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_4'('#skF_5', '#skF_6')), '#skF_4'('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_71, c_430])).
% 7.57/2.58  tff(c_42, plain, (![D_57, A_44, B_52]: (v4_pre_topc(D_57, A_44) | ~r2_hidden(D_57, '#skF_4'(A_44, B_52)) | ~m1_subset_1(D_57, k1_zfmisc_1(u1_struct_0(A_44))) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_44))) | ~l1_pre_topc(A_44) | ~v2_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_114])).
% 7.57/2.58  tff(c_433, plain, (v4_pre_topc('#skF_2'('#skF_5', '#skF_4'('#skF_5', '#skF_6')), '#skF_5') | ~m1_subset_1('#skF_2'('#skF_5', '#skF_4'('#skF_5', '#skF_6')), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_431, c_42])).
% 7.57/2.58  tff(c_440, plain, (v4_pre_topc('#skF_2'('#skF_5', '#skF_4'('#skF_5', '#skF_6')), '#skF_5') | ~m1_subset_1('#skF_2'('#skF_5', '#skF_4'('#skF_5', '#skF_6')), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_48, c_46, c_433])).
% 7.57/2.58  tff(c_441, plain, (~m1_subset_1('#skF_2'('#skF_5', '#skF_4'('#skF_5', '#skF_6')), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_300, c_440])).
% 7.57/2.58  tff(c_448, plain, (v4_pre_topc(k6_setfam_1(u1_struct_0('#skF_5'), '#skF_4'('#skF_5', '#skF_6')), '#skF_5') | ~m1_subset_1('#skF_4'('#skF_5', '#skF_6'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5')))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_22, c_441])).
% 7.57/2.58  tff(c_451, plain, (v4_pre_topc('#skF_6', '#skF_5') | ~m1_subset_1('#skF_4'('#skF_5', '#skF_6'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_48, c_138, c_448])).
% 7.57/2.58  tff(c_452, plain, (~m1_subset_1('#skF_4'('#skF_5', '#skF_6'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_71, c_451])).
% 7.57/2.58  tff(c_455, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_36, c_452])).
% 7.57/2.58  tff(c_459, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_63, c_48, c_46, c_455])).
% 7.57/2.58  tff(c_461, plain, (k2_pre_topc('#skF_5', '#skF_6')!='#skF_6'), inference(splitRight, [status(thm)], [c_56])).
% 7.57/2.58  tff(c_472, plain, (![B_170, A_171]: (r1_tarski(B_170, k2_pre_topc(A_171, B_170)) | ~m1_subset_1(B_170, k1_zfmisc_1(u1_struct_0(A_171))) | ~l1_pre_topc(A_171))), inference(cnfTransformation, [status(thm)], [f_121])).
% 7.57/2.58  tff(c_474, plain, (r1_tarski('#skF_6', k2_pre_topc('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_46, c_472])).
% 7.57/2.58  tff(c_477, plain, (r1_tarski('#skF_6', k2_pre_topc('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_474])).
% 7.57/2.58  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.57/2.58  tff(c_479, plain, (k2_pre_topc('#skF_5', '#skF_6')='#skF_6' | ~r1_tarski(k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')), inference(resolution, [status(thm)], [c_477, c_2])).
% 7.57/2.58  tff(c_482, plain, (~r1_tarski(k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_461, c_479])).
% 7.57/2.58  tff(c_460, plain, (v4_pre_topc('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_56])).
% 7.57/2.58  tff(c_16, plain, (![A_14, B_15]: (m1_subset_1(k2_pre_topc(A_14, B_15), k1_zfmisc_1(u1_struct_0(A_14))) | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.57/2.58  tff(c_493, plain, (![A_181, B_182, C_183]: (r2_hidden('#skF_1'(A_181, B_182, C_183), B_182) | r1_tarski(B_182, C_183) | ~m1_subset_1(C_183, k1_zfmisc_1(A_181)) | ~m1_subset_1(B_182, k1_zfmisc_1(A_181)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.57/2.58  tff(c_8, plain, (![C_6, A_3, B_4]: (r2_hidden(C_6, A_3) | ~r2_hidden(C_6, B_4) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.57/2.58  tff(c_502, plain, (![A_181, B_182, C_183, A_3]: (r2_hidden('#skF_1'(A_181, B_182, C_183), A_3) | ~m1_subset_1(B_182, k1_zfmisc_1(A_3)) | r1_tarski(B_182, C_183) | ~m1_subset_1(C_183, k1_zfmisc_1(A_181)) | ~m1_subset_1(B_182, k1_zfmisc_1(A_181)))), inference(resolution, [status(thm)], [c_493, c_8])).
% 7.57/2.58  tff(c_12, plain, (![A_7, B_8, C_12]: (r2_hidden('#skF_1'(A_7, B_8, C_12), B_8) | r1_tarski(B_8, C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(A_7)) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.57/2.58  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.57/2.58  tff(c_826, plain, (![C_250, D_251, B_252, A_253]: (r2_hidden(C_250, D_251) | ~r1_tarski(B_252, D_251) | ~v4_pre_topc(D_251, A_253) | ~m1_subset_1(D_251, k1_zfmisc_1(u1_struct_0(A_253))) | ~r2_hidden(C_250, k2_pre_topc(A_253, B_252)) | ~r2_hidden(C_250, u1_struct_0(A_253)) | ~m1_subset_1(B_252, k1_zfmisc_1(u1_struct_0(A_253))) | ~l1_pre_topc(A_253))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.57/2.58  tff(c_836, plain, (![C_254, B_255, A_256]: (r2_hidden(C_254, B_255) | ~v4_pre_topc(B_255, A_256) | ~r2_hidden(C_254, k2_pre_topc(A_256, B_255)) | ~r2_hidden(C_254, u1_struct_0(A_256)) | ~m1_subset_1(B_255, k1_zfmisc_1(u1_struct_0(A_256))) | ~l1_pre_topc(A_256))), inference(resolution, [status(thm)], [c_6, c_826])).
% 7.57/2.58  tff(c_1618, plain, (![A_548, A_549, B_550, C_551]: (r2_hidden('#skF_1'(A_548, k2_pre_topc(A_549, B_550), C_551), B_550) | ~v4_pre_topc(B_550, A_549) | ~r2_hidden('#skF_1'(A_548, k2_pre_topc(A_549, B_550), C_551), u1_struct_0(A_549)) | ~m1_subset_1(B_550, k1_zfmisc_1(u1_struct_0(A_549))) | ~l1_pre_topc(A_549) | r1_tarski(k2_pre_topc(A_549, B_550), C_551) | ~m1_subset_1(C_551, k1_zfmisc_1(A_548)) | ~m1_subset_1(k2_pre_topc(A_549, B_550), k1_zfmisc_1(A_548)))), inference(resolution, [status(thm)], [c_12, c_836])).
% 7.57/2.58  tff(c_1696, plain, (![A_561, A_562, B_563, C_564]: (r2_hidden('#skF_1'(A_561, k2_pre_topc(A_562, B_563), C_564), B_563) | ~v4_pre_topc(B_563, A_562) | ~m1_subset_1(B_563, k1_zfmisc_1(u1_struct_0(A_562))) | ~l1_pre_topc(A_562) | ~m1_subset_1(k2_pre_topc(A_562, B_563), k1_zfmisc_1(u1_struct_0(A_562))) | r1_tarski(k2_pre_topc(A_562, B_563), C_564) | ~m1_subset_1(C_564, k1_zfmisc_1(A_561)) | ~m1_subset_1(k2_pre_topc(A_562, B_563), k1_zfmisc_1(A_561)))), inference(resolution, [status(thm)], [c_502, c_1618])).
% 7.57/2.58  tff(c_1700, plain, (![A_565, A_566, B_567, C_568]: (r2_hidden('#skF_1'(A_565, k2_pre_topc(A_566, B_567), C_568), B_567) | ~v4_pre_topc(B_567, A_566) | r1_tarski(k2_pre_topc(A_566, B_567), C_568) | ~m1_subset_1(C_568, k1_zfmisc_1(A_565)) | ~m1_subset_1(k2_pre_topc(A_566, B_567), k1_zfmisc_1(A_565)) | ~m1_subset_1(B_567, k1_zfmisc_1(u1_struct_0(A_566))) | ~l1_pre_topc(A_566))), inference(resolution, [status(thm)], [c_16, c_1696])).
% 7.57/2.58  tff(c_10, plain, (![A_7, B_8, C_12]: (~r2_hidden('#skF_1'(A_7, B_8, C_12), C_12) | r1_tarski(B_8, C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(A_7)) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.57/2.58  tff(c_1735, plain, (![B_569, A_570, A_571]: (~v4_pre_topc(B_569, A_570) | r1_tarski(k2_pre_topc(A_570, B_569), B_569) | ~m1_subset_1(B_569, k1_zfmisc_1(A_571)) | ~m1_subset_1(k2_pre_topc(A_570, B_569), k1_zfmisc_1(A_571)) | ~m1_subset_1(B_569, k1_zfmisc_1(u1_struct_0(A_570))) | ~l1_pre_topc(A_570))), inference(resolution, [status(thm)], [c_1700, c_10])).
% 7.57/2.58  tff(c_1739, plain, (![B_572, A_573]: (~v4_pre_topc(B_572, A_573) | r1_tarski(k2_pre_topc(A_573, B_572), B_572) | ~m1_subset_1(B_572, k1_zfmisc_1(u1_struct_0(A_573))) | ~l1_pre_topc(A_573))), inference(resolution, [status(thm)], [c_16, c_1735])).
% 7.57/2.58  tff(c_1750, plain, (~v4_pre_topc('#skF_6', '#skF_5') | r1_tarski(k2_pre_topc('#skF_5', '#skF_6'), '#skF_6') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_46, c_1739])).
% 7.57/2.58  tff(c_1757, plain, (r1_tarski(k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_460, c_1750])).
% 7.57/2.58  tff(c_1759, plain, $false, inference(negUnitSimplification, [status(thm)], [c_482, c_1757])).
% 7.57/2.58  tff(c_1761, plain, (~v2_pre_topc('#skF_5')), inference(splitRight, [status(thm)], [c_60])).
% 7.57/2.58  tff(c_58, plain, (k2_pre_topc('#skF_5', '#skF_6')!='#skF_6' | v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_137])).
% 7.57/2.58  tff(c_1762, plain, (k2_pre_topc('#skF_5', '#skF_6')!='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_1761, c_58])).
% 7.57/2.58  tff(c_1775, plain, (![B_579, A_580]: (r1_tarski(B_579, k2_pre_topc(A_580, B_579)) | ~m1_subset_1(B_579, k1_zfmisc_1(u1_struct_0(A_580))) | ~l1_pre_topc(A_580))), inference(cnfTransformation, [status(thm)], [f_121])).
% 7.57/2.58  tff(c_1777, plain, (r1_tarski('#skF_6', k2_pre_topc('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_46, c_1775])).
% 7.57/2.58  tff(c_1780, plain, (r1_tarski('#skF_6', k2_pre_topc('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1777])).
% 7.57/2.58  tff(c_1782, plain, (k2_pre_topc('#skF_5', '#skF_6')='#skF_6' | ~r1_tarski(k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')), inference(resolution, [status(thm)], [c_1780, c_2])).
% 7.57/2.58  tff(c_1785, plain, (~r1_tarski(k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_1762, c_1782])).
% 7.57/2.58  tff(c_1760, plain, (v4_pre_topc('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_60])).
% 7.57/2.58  tff(c_1795, plain, (![A_588, B_589, C_590]: (r2_hidden('#skF_1'(A_588, B_589, C_590), B_589) | r1_tarski(B_589, C_590) | ~m1_subset_1(C_590, k1_zfmisc_1(A_588)) | ~m1_subset_1(B_589, k1_zfmisc_1(A_588)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.57/2.58  tff(c_1804, plain, (![A_588, B_589, C_590, A_3]: (r2_hidden('#skF_1'(A_588, B_589, C_590), A_3) | ~m1_subset_1(B_589, k1_zfmisc_1(A_3)) | r1_tarski(B_589, C_590) | ~m1_subset_1(C_590, k1_zfmisc_1(A_588)) | ~m1_subset_1(B_589, k1_zfmisc_1(A_588)))), inference(resolution, [status(thm)], [c_1795, c_8])).
% 7.57/2.58  tff(c_2072, plain, (![C_677, D_678, B_679, A_680]: (r2_hidden(C_677, D_678) | ~r1_tarski(B_679, D_678) | ~v4_pre_topc(D_678, A_680) | ~m1_subset_1(D_678, k1_zfmisc_1(u1_struct_0(A_680))) | ~r2_hidden(C_677, k2_pre_topc(A_680, B_679)) | ~r2_hidden(C_677, u1_struct_0(A_680)) | ~m1_subset_1(B_679, k1_zfmisc_1(u1_struct_0(A_680))) | ~l1_pre_topc(A_680))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.57/2.58  tff(c_2091, plain, (![C_681, B_682, A_683]: (r2_hidden(C_681, B_682) | ~v4_pre_topc(B_682, A_683) | ~r2_hidden(C_681, k2_pre_topc(A_683, B_682)) | ~r2_hidden(C_681, u1_struct_0(A_683)) | ~m1_subset_1(B_682, k1_zfmisc_1(u1_struct_0(A_683))) | ~l1_pre_topc(A_683))), inference(resolution, [status(thm)], [c_6, c_2072])).
% 7.57/2.58  tff(c_2692, plain, (![A_935, A_936, B_937, C_938]: (r2_hidden('#skF_1'(A_935, k2_pre_topc(A_936, B_937), C_938), B_937) | ~v4_pre_topc(B_937, A_936) | ~r2_hidden('#skF_1'(A_935, k2_pre_topc(A_936, B_937), C_938), u1_struct_0(A_936)) | ~m1_subset_1(B_937, k1_zfmisc_1(u1_struct_0(A_936))) | ~l1_pre_topc(A_936) | r1_tarski(k2_pre_topc(A_936, B_937), C_938) | ~m1_subset_1(C_938, k1_zfmisc_1(A_935)) | ~m1_subset_1(k2_pre_topc(A_936, B_937), k1_zfmisc_1(A_935)))), inference(resolution, [status(thm)], [c_12, c_2091])).
% 7.57/2.58  tff(c_2745, plain, (![A_944, A_945, B_946, C_947]: (r2_hidden('#skF_1'(A_944, k2_pre_topc(A_945, B_946), C_947), B_946) | ~v4_pre_topc(B_946, A_945) | ~m1_subset_1(B_946, k1_zfmisc_1(u1_struct_0(A_945))) | ~l1_pre_topc(A_945) | ~m1_subset_1(k2_pre_topc(A_945, B_946), k1_zfmisc_1(u1_struct_0(A_945))) | r1_tarski(k2_pre_topc(A_945, B_946), C_947) | ~m1_subset_1(C_947, k1_zfmisc_1(A_944)) | ~m1_subset_1(k2_pre_topc(A_945, B_946), k1_zfmisc_1(A_944)))), inference(resolution, [status(thm)], [c_1804, c_2692])).
% 7.57/2.58  tff(c_2749, plain, (![A_948, A_949, B_950, C_951]: (r2_hidden('#skF_1'(A_948, k2_pre_topc(A_949, B_950), C_951), B_950) | ~v4_pre_topc(B_950, A_949) | r1_tarski(k2_pre_topc(A_949, B_950), C_951) | ~m1_subset_1(C_951, k1_zfmisc_1(A_948)) | ~m1_subset_1(k2_pre_topc(A_949, B_950), k1_zfmisc_1(A_948)) | ~m1_subset_1(B_950, k1_zfmisc_1(u1_struct_0(A_949))) | ~l1_pre_topc(A_949))), inference(resolution, [status(thm)], [c_16, c_2745])).
% 7.57/2.58  tff(c_2784, plain, (![B_952, A_953, A_954]: (~v4_pre_topc(B_952, A_953) | r1_tarski(k2_pre_topc(A_953, B_952), B_952) | ~m1_subset_1(B_952, k1_zfmisc_1(A_954)) | ~m1_subset_1(k2_pre_topc(A_953, B_952), k1_zfmisc_1(A_954)) | ~m1_subset_1(B_952, k1_zfmisc_1(u1_struct_0(A_953))) | ~l1_pre_topc(A_953))), inference(resolution, [status(thm)], [c_2749, c_10])).
% 7.57/2.58  tff(c_2788, plain, (![B_955, A_956]: (~v4_pre_topc(B_955, A_956) | r1_tarski(k2_pre_topc(A_956, B_955), B_955) | ~m1_subset_1(B_955, k1_zfmisc_1(u1_struct_0(A_956))) | ~l1_pre_topc(A_956))), inference(resolution, [status(thm)], [c_16, c_2784])).
% 7.57/2.58  tff(c_2799, plain, (~v4_pre_topc('#skF_6', '#skF_5') | r1_tarski(k2_pre_topc('#skF_5', '#skF_6'), '#skF_6') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_46, c_2788])).
% 7.57/2.58  tff(c_2806, plain, (r1_tarski(k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1760, c_2799])).
% 7.57/2.58  tff(c_2808, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1785, c_2806])).
% 7.57/2.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.57/2.58  
% 7.57/2.58  Inference rules
% 7.57/2.58  ----------------------
% 7.57/2.58  #Ref     : 0
% 7.57/2.58  #Sup     : 628
% 7.57/2.58  #Fact    : 0
% 7.57/2.58  #Define  : 0
% 7.57/2.58  #Split   : 13
% 7.57/2.58  #Chain   : 0
% 7.57/2.58  #Close   : 0
% 7.57/2.58  
% 7.57/2.58  Ordering : KBO
% 7.57/2.58  
% 7.57/2.58  Simplification rules
% 7.57/2.58  ----------------------
% 7.57/2.58  #Subsume      : 63
% 7.57/2.58  #Demod        : 245
% 7.57/2.58  #Tautology    : 72
% 7.57/2.58  #SimpNegUnit  : 11
% 7.57/2.58  #BackRed      : 0
% 7.57/2.58  
% 7.57/2.58  #Partial instantiations: 0
% 7.57/2.58  #Strategies tried      : 1
% 7.57/2.58  
% 7.57/2.58  Timing (in seconds)
% 7.57/2.58  ----------------------
% 7.57/2.59  Preprocessing        : 0.32
% 7.57/2.59  Parsing              : 0.17
% 7.57/2.59  CNF conversion       : 0.03
% 7.57/2.59  Main loop            : 1.48
% 7.57/2.59  Inferencing          : 0.55
% 7.57/2.59  Reduction            : 0.37
% 7.57/2.59  Demodulation         : 0.23
% 7.57/2.59  BG Simplification    : 0.05
% 7.57/2.59  Subsumption          : 0.41
% 7.57/2.59  Abstraction          : 0.06
% 7.57/2.59  MUC search           : 0.00
% 7.57/2.59  Cooper               : 0.00
% 7.57/2.59  Total                : 1.85
% 7.57/2.59  Index Insertion      : 0.00
% 7.57/2.59  Index Deletion       : 0.00
% 7.57/2.59  Index Matching       : 0.00
% 7.57/2.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
