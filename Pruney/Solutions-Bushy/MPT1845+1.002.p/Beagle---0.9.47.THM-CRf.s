%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1845+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:32 EST 2020

% Result     : Theorem 7.10s
% Output     : CNFRefutation 7.53s
% Verified   : 
% Statistics : Number of formulae       :  198 (5560 expanded)
%              Number of leaves         :   29 (1746 expanded)
%              Depth                    :   19
%              Number of atoms          :  475 (15791 expanded)
%              Number of equality atoms :   43 (5703 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k9_subset_1 > k5_setfam_1 > k3_xboole_0 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_5 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( l1_pre_topc(B)
           => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                & v2_pre_topc(A) )
             => v2_pre_topc(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_tex_2)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_pre_topc(A)
      <=> ( r2_hidden(u1_struct_0(A),u1_pre_topc(A))
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( r1_tarski(B,u1_pre_topc(A))
               => r2_hidden(k5_setfam_1(u1_struct_0(A),B),u1_pre_topc(A)) ) )
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
             => ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r2_hidden(B,u1_pre_topc(A))
                      & r2_hidden(C,u1_pre_topc(A)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(A),B,C),u1_pre_topc(A)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_82,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v1_pre_topc(g1_pre_topc(A,B))
        & l1_pre_topc(g1_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

tff(f_73,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).

tff(f_30,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(c_56,plain,(
    ~ v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_62,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_64,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_58,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_38,plain,(
    ! [A_2] :
      ( r2_hidden(u1_struct_0(A_2),u1_pre_topc(A_2))
      | ~ v2_pre_topc(A_2)
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_44,plain,(
    ! [A_18] :
      ( m1_subset_1(u1_pre_topc(A_18),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_18))))
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_60,plain,(
    g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')) = g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_146,plain,(
    ! [C_43,A_44,D_45,B_46] :
      ( C_43 = A_44
      | g1_pre_topc(C_43,D_45) != g1_pre_topc(A_44,B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(k1_zfmisc_1(A_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_188,plain,(
    ! [A_56,B_57] :
      ( u1_struct_0('#skF_5') = A_56
      | g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) != g1_pre_topc(A_56,B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(k1_zfmisc_1(A_56))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_146])).

tff(c_192,plain,(
    ! [A_18] :
      ( u1_struct_0(A_18) = u1_struct_0('#skF_5')
      | g1_pre_topc(u1_struct_0(A_18),u1_pre_topc(A_18)) != g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))
      | ~ l1_pre_topc(A_18) ) ),
    inference(resolution,[status(thm)],[c_44,c_188])).

tff(c_216,plain,
    ( u1_struct_0('#skF_5') = u1_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_192])).

tff(c_218,plain,(
    u1_struct_0('#skF_5') = u1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_216])).

tff(c_159,plain,(
    ! [D_47,B_48,C_49,A_50] :
      ( D_47 = B_48
      | g1_pre_topc(C_49,D_47) != g1_pre_topc(A_50,B_48)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(k1_zfmisc_1(A_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_167,plain,(
    ! [D_47,C_49] :
      ( u1_pre_topc('#skF_5') = D_47
      | g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) != g1_pre_topc(C_49,D_47)
      | ~ m1_subset_1(u1_pre_topc('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_159])).

tff(c_235,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5')))) ),
    inference(splitLeft,[status(thm)],[c_167])).

tff(c_284,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_235])).

tff(c_263,plain,
    ( m1_subset_1(u1_pre_topc('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_44])).

tff(c_282,plain,(
    m1_subset_1(u1_pre_topc('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_263])).

tff(c_285,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_284,c_282])).

tff(c_286,plain,(
    ! [D_47,C_49] :
      ( u1_pre_topc('#skF_5') = D_47
      | g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) != g1_pre_topc(C_49,D_47) ) ),
    inference(splitRight,[status(thm)],[c_167])).

tff(c_391,plain,(
    u1_pre_topc('#skF_5') = u1_pre_topc('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_286])).

tff(c_18,plain,(
    ! [A_2] :
      ( r1_tarski('#skF_1'(A_2),u1_pre_topc(A_2))
      | r2_hidden('#skF_2'(A_2),u1_pre_topc(A_2))
      | v2_pre_topc(A_2)
      | ~ r2_hidden(u1_struct_0(A_2),u1_pre_topc(A_2))
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_415,plain,
    ( r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_5'))
    | r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_5'))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_4'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_391,c_18])).

tff(c_443,plain,
    ( r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_4'))
    | r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_4'))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_218,c_391,c_391,c_415])).

tff(c_444,plain,
    ( r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_4'))
    | r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_4'))
    | ~ r2_hidden(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_443])).

tff(c_486,plain,(
    ~ r2_hidden(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_444])).

tff(c_489,plain,
    ( ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_486])).

tff(c_493,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_58,c_489])).

tff(c_495,plain,(
    r2_hidden(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_444])).

tff(c_1189,plain,(
    ! [A_105] :
      ( m1_subset_1('#skF_1'(A_105),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_105))))
      | m1_subset_1('#skF_2'(A_105),k1_zfmisc_1(u1_struct_0(A_105)))
      | v2_pre_topc(A_105)
      | ~ r2_hidden(u1_struct_0(A_105),u1_pre_topc(A_105))
      | ~ l1_pre_topc(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1209,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | m1_subset_1('#skF_2'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_1189])).

tff(c_1218,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | m1_subset_1('#skF_2'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_495,c_218,c_391,c_218,c_1209])).

tff(c_1219,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | m1_subset_1('#skF_2'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1218])).

tff(c_1220,plain,(
    m1_subset_1('#skF_2'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_1219])).

tff(c_636,plain,(
    ! [A_74] :
      ( m1_subset_1('#skF_1'(A_74),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_74))))
      | r2_hidden('#skF_2'(A_74),u1_pre_topc(A_74))
      | v2_pre_topc(A_74)
      | ~ r2_hidden(u1_struct_0(A_74),u1_pre_topc(A_74))
      | ~ l1_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_647,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_5'))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_636])).

tff(c_652,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_4'))
    | v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_495,c_218,c_391,c_391,c_647])).

tff(c_653,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_652])).

tff(c_672,plain,(
    r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_653])).

tff(c_926,plain,(
    ! [A_85] :
      ( m1_subset_1('#skF_1'(A_85),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_85))))
      | m1_subset_1('#skF_3'(A_85),k1_zfmisc_1(u1_struct_0(A_85)))
      | v2_pre_topc(A_85)
      | ~ r2_hidden(u1_struct_0(A_85),u1_pre_topc(A_85))
      | ~ l1_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_940,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | m1_subset_1('#skF_3'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_926])).

tff(c_947,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | m1_subset_1('#skF_3'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_495,c_218,c_391,c_218,c_940])).

tff(c_948,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | m1_subset_1('#skF_3'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_947])).

tff(c_949,plain,(
    m1_subset_1('#skF_3'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_948])).

tff(c_883,plain,(
    ! [A_82] :
      ( m1_subset_1('#skF_1'(A_82),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_82))))
      | r2_hidden('#skF_3'(A_82),u1_pre_topc(A_82))
      | v2_pre_topc(A_82)
      | ~ r2_hidden(u1_struct_0(A_82),u1_pre_topc(A_82))
      | ~ l1_pre_topc(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_897,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_5'))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_883])).

tff(c_904,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_4'))
    | v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_495,c_218,c_391,c_391,c_897])).

tff(c_905,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_904])).

tff(c_906,plain,(
    r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_905])).

tff(c_54,plain,(
    ! [A_26,B_27,C_28] :
      ( k9_subset_1(A_26,B_27,C_28) = k3_xboole_0(B_27,C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(A_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_952,plain,(
    ! [B_27] : k9_subset_1(u1_struct_0('#skF_4'),B_27,'#skF_3'('#skF_5')) = k3_xboole_0(B_27,'#skF_3'('#skF_5')) ),
    inference(resolution,[status(thm)],[c_949,c_54])).

tff(c_2742,plain,(
    ! [A_144,B_145,C_146] :
      ( r2_hidden(k9_subset_1(u1_struct_0(A_144),B_145,C_146),u1_pre_topc(A_144))
      | ~ r2_hidden(C_146,u1_pre_topc(A_144))
      | ~ r2_hidden(B_145,u1_pre_topc(A_144))
      | ~ m1_subset_1(C_146,k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ v2_pre_topc(A_144)
      | ~ l1_pre_topc(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2769,plain,(
    ! [B_27] :
      ( r2_hidden(k3_xboole_0(B_27,'#skF_3'('#skF_5')),u1_pre_topc('#skF_4'))
      | ~ r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_4'))
      | ~ r2_hidden(B_27,u1_pre_topc('#skF_4'))
      | ~ m1_subset_1('#skF_3'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_pre_topc('#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_952,c_2742])).

tff(c_2798,plain,(
    ! [B_148] :
      ( r2_hidden(k3_xboole_0(B_148,'#skF_3'('#skF_5')),u1_pre_topc('#skF_4'))
      | ~ r2_hidden(B_148,u1_pre_topc('#skF_4'))
      | ~ m1_subset_1(B_148,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_58,c_949,c_906,c_2769])).

tff(c_2351,plain,(
    ! [A_133] :
      ( m1_subset_1('#skF_1'(A_133),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_133))))
      | ~ r2_hidden(k9_subset_1(u1_struct_0(A_133),'#skF_2'(A_133),'#skF_3'(A_133)),u1_pre_topc(A_133))
      | v2_pre_topc(A_133)
      | ~ r2_hidden(u1_struct_0(A_133),u1_pre_topc(A_133))
      | ~ l1_pre_topc(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2366,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5'))))
    | ~ r2_hidden(k9_subset_1(u1_struct_0('#skF_5'),'#skF_2'('#skF_5'),'#skF_3'('#skF_5')),u1_pre_topc('#skF_4'))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_391,c_2351])).

tff(c_2375,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ r2_hidden(k3_xboole_0('#skF_2'('#skF_5'),'#skF_3'('#skF_5')),u1_pre_topc('#skF_4'))
    | v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_495,c_218,c_391,c_952,c_218,c_218,c_2366])).

tff(c_2376,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ r2_hidden(k3_xboole_0('#skF_2'('#skF_5'),'#skF_3'('#skF_5')),u1_pre_topc('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2375])).

tff(c_2380,plain,(
    ~ r2_hidden(k3_xboole_0('#skF_2'('#skF_5'),'#skF_3'('#skF_5')),u1_pre_topc('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_2376])).

tff(c_2801,plain,
    ( ~ r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_4'))
    | ~ m1_subset_1('#skF_2'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_2798,c_2380])).

tff(c_2805,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1220,c_672,c_2801])).

tff(c_2806,plain,(
    m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(splitRight,[status(thm)],[c_2376])).

tff(c_494,plain,
    ( r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_4'))
    | r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_444])).

tff(c_508,plain,(
    r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_494])).

tff(c_73,plain,(
    ! [A_35,B_36] :
      ( l1_pre_topc(g1_pre_topc(A_35,B_36))
      | ~ m1_subset_1(B_36,k1_zfmisc_1(k1_zfmisc_1(A_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_87,plain,(
    ! [A_37] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_37),u1_pre_topc(A_37)))
      | ~ l1_pre_topc(A_37) ) ),
    inference(resolution,[status(thm)],[c_44,c_73])).

tff(c_90,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_87])).

tff(c_92,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_90])).

tff(c_46,plain,(
    ! [A_19] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(A_19),u1_pre_topc(A_19)))
      | ~ l1_pre_topc(A_19)
      | ~ v2_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_66,plain,(
    ! [A_31,B_32] :
      ( v1_pre_topc(g1_pre_topc(A_31,B_32))
      | ~ m1_subset_1(B_32,k1_zfmisc_1(k1_zfmisc_1(A_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_70,plain,(
    ! [A_18] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_18),u1_pre_topc(A_18)))
      | ~ l1_pre_topc(A_18) ) ),
    inference(resolution,[status(thm)],[c_44,c_66])).

tff(c_81,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_70])).

tff(c_85,plain,(
    v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_81])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) = A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_392,plain,(
    ! [D_66,C_67] :
      ( u1_pre_topc('#skF_5') = D_66
      | g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) != g1_pre_topc(C_67,D_66) ) ),
    inference(splitRight,[status(thm)],[c_167])).

tff(c_401,plain,(
    ! [A_1] :
      ( u1_pre_topc(A_1) = u1_pre_topc('#skF_5')
      | g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) != A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_392])).

tff(c_559,plain,(
    ! [A_1] :
      ( u1_pre_topc(A_1) = u1_pre_topc('#skF_4')
      | g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) != A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_391,c_401])).

tff(c_563,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) = u1_pre_topc('#skF_4')
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_559])).

tff(c_565,plain,(
    u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) = u1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_85,c_563])).

tff(c_593,plain,
    ( r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))),u1_pre_topc('#skF_4'))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_565,c_38])).

tff(c_618,plain,
    ( r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))),u1_pre_topc('#skF_4'))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_593])).

tff(c_745,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_618])).

tff(c_751,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_745])).

tff(c_757,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_64,c_751])).

tff(c_759,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_618])).

tff(c_599,plain,
    ( m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_565,c_44])).

tff(c_622,plain,(
    m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_599])).

tff(c_584,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))),u1_pre_topc('#skF_4')) = g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_565,c_2])).

tff(c_612,plain,(
    g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))),u1_pre_topc('#skF_4')) = g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_85,c_584])).

tff(c_52,plain,(
    ! [C_24,A_20,D_25,B_21] :
      ( C_24 = A_20
      | g1_pre_topc(C_24,D_25) != g1_pre_topc(A_20,B_21)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k1_zfmisc_1(A_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_695,plain,(
    ! [C_24,D_25] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) = C_24
      | g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) != g1_pre_topc(C_24,D_25)
      | ~ m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_612,c_52])).

tff(c_709,plain,(
    ! [C_24,D_25] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) = C_24
      | g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) != g1_pre_topc(C_24,D_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_622,c_695])).

tff(c_775,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) = u1_struct_0('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_709])).

tff(c_36,plain,(
    ! [A_2,B_11] :
      ( r2_hidden(k5_setfam_1(u1_struct_0(A_2),B_11),u1_pre_topc(A_2))
      | ~ r1_tarski(B_11,u1_pre_topc(A_2))
      | ~ m1_subset_1(B_11,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_2))))
      | ~ v2_pre_topc(A_2)
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_799,plain,(
    ! [B_11] :
      ( r2_hidden(k5_setfam_1(u1_struct_0('#skF_4'),B_11),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))
      | ~ r1_tarski(B_11,u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))
      | ~ m1_subset_1(B_11,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_775,c_36])).

tff(c_842,plain,(
    ! [B_11] :
      ( r2_hidden(k5_setfam_1(u1_struct_0('#skF_4'),B_11),u1_pre_topc('#skF_4'))
      | ~ r1_tarski(B_11,u1_pre_topc('#skF_4'))
      | ~ m1_subset_1(B_11,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_759,c_775,c_565,c_565,c_799])).

tff(c_2807,plain,(
    r2_hidden(k3_xboole_0('#skF_2'('#skF_5'),'#skF_3'('#skF_5')),u1_pre_topc('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2376])).

tff(c_3081,plain,(
    ! [A_150] :
      ( ~ r2_hidden(k5_setfam_1(u1_struct_0(A_150),'#skF_1'(A_150)),u1_pre_topc(A_150))
      | ~ r2_hidden(k9_subset_1(u1_struct_0(A_150),'#skF_2'(A_150),'#skF_3'(A_150)),u1_pre_topc(A_150))
      | v2_pre_topc(A_150)
      | ~ r2_hidden(u1_struct_0(A_150),u1_pre_topc(A_150))
      | ~ l1_pre_topc(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3099,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0('#skF_5'),'#skF_1'('#skF_5')),u1_pre_topc('#skF_5'))
    | ~ r2_hidden(k9_subset_1(u1_struct_0('#skF_5'),'#skF_2'('#skF_5'),'#skF_3'('#skF_5')),u1_pre_topc('#skF_4'))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_391,c_3081])).

tff(c_3110,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0('#skF_4'),'#skF_1'('#skF_5')),u1_pre_topc('#skF_4'))
    | v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_495,c_218,c_391,c_2807,c_952,c_218,c_218,c_391,c_3099])).

tff(c_3111,plain,(
    ~ r2_hidden(k5_setfam_1(u1_struct_0('#skF_4'),'#skF_1'('#skF_5')),u1_pre_topc('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_3110])).

tff(c_3117,plain,
    ( ~ r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_4'))
    | ~ m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(resolution,[status(thm)],[c_842,c_3111])).

tff(c_3124,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2806,c_508,c_3117])).

tff(c_3125,plain,(
    m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(splitRight,[status(thm)],[c_1219])).

tff(c_3126,plain,(
    ~ m1_subset_1('#skF_2'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_1219])).

tff(c_3281,plain,(
    ! [A_152] :
      ( ~ r2_hidden(k5_setfam_1(u1_struct_0(A_152),'#skF_1'(A_152)),u1_pre_topc(A_152))
      | m1_subset_1('#skF_2'(A_152),k1_zfmisc_1(u1_struct_0(A_152)))
      | v2_pre_topc(A_152)
      | ~ r2_hidden(u1_struct_0(A_152),u1_pre_topc(A_152))
      | ~ l1_pre_topc(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3301,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0('#skF_5'),'#skF_1'('#skF_5')),u1_pre_topc('#skF_4'))
    | m1_subset_1('#skF_2'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_391,c_3281])).

tff(c_3316,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0('#skF_4'),'#skF_1'('#skF_5')),u1_pre_topc('#skF_4'))
    | m1_subset_1('#skF_2'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_495,c_218,c_391,c_218,c_218,c_3301])).

tff(c_3317,plain,(
    ~ r2_hidden(k5_setfam_1(u1_struct_0('#skF_4'),'#skF_1'('#skF_5')),u1_pre_topc('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_3126,c_3316])).

tff(c_3323,plain,
    ( ~ r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_4'))
    | ~ m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(resolution,[status(thm)],[c_842,c_3317])).

tff(c_3330,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3125,c_508,c_3323])).

tff(c_3331,plain,(
    m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(splitRight,[status(thm)],[c_948])).

tff(c_3332,plain,(
    ~ m1_subset_1('#skF_3'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_948])).

tff(c_3900,plain,(
    ! [A_175] :
      ( ~ r2_hidden(k5_setfam_1(u1_struct_0(A_175),'#skF_1'(A_175)),u1_pre_topc(A_175))
      | m1_subset_1('#skF_3'(A_175),k1_zfmisc_1(u1_struct_0(A_175)))
      | v2_pre_topc(A_175)
      | ~ r2_hidden(u1_struct_0(A_175),u1_pre_topc(A_175))
      | ~ l1_pre_topc(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3923,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0('#skF_5'),'#skF_1'('#skF_5')),u1_pre_topc('#skF_4'))
    | m1_subset_1('#skF_3'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_391,c_3900])).

tff(c_3942,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0('#skF_4'),'#skF_1'('#skF_5')),u1_pre_topc('#skF_4'))
    | m1_subset_1('#skF_3'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_495,c_218,c_391,c_218,c_218,c_3923])).

tff(c_3943,plain,(
    ~ r2_hidden(k5_setfam_1(u1_struct_0('#skF_4'),'#skF_1'('#skF_5')),u1_pre_topc('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_3332,c_3942])).

tff(c_3949,plain,
    ( ~ r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_4'))
    | ~ m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(resolution,[status(thm)],[c_842,c_3943])).

tff(c_3956,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3331,c_508,c_3949])).

tff(c_3957,plain,(
    m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(splitRight,[status(thm)],[c_905])).

tff(c_3958,plain,(
    ~ r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_905])).

tff(c_4479,plain,(
    ! [A_198] :
      ( ~ r2_hidden(k5_setfam_1(u1_struct_0(A_198),'#skF_1'(A_198)),u1_pre_topc(A_198))
      | r2_hidden('#skF_3'(A_198),u1_pre_topc(A_198))
      | v2_pre_topc(A_198)
      | ~ r2_hidden(u1_struct_0(A_198),u1_pre_topc(A_198))
      | ~ l1_pre_topc(A_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4502,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0('#skF_5'),'#skF_1'('#skF_5')),u1_pre_topc('#skF_4'))
    | r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_5'))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_391,c_4479])).

tff(c_4521,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0('#skF_4'),'#skF_1'('#skF_5')),u1_pre_topc('#skF_4'))
    | r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_4'))
    | v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_495,c_218,c_391,c_391,c_218,c_4502])).

tff(c_4522,plain,(
    ~ r2_hidden(k5_setfam_1(u1_struct_0('#skF_4'),'#skF_1'('#skF_5')),u1_pre_topc('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_3958,c_4521])).

tff(c_4528,plain,
    ( ~ r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_4'))
    | ~ m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(resolution,[status(thm)],[c_842,c_4522])).

tff(c_4535,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3957,c_508,c_4528])).

tff(c_4537,plain,(
    ~ r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_653])).

tff(c_4536,plain,(
    m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(splitRight,[status(thm)],[c_653])).

tff(c_4810,plain,(
    ! [A_209] :
      ( ~ r2_hidden(k5_setfam_1(u1_struct_0(A_209),'#skF_1'(A_209)),u1_pre_topc(A_209))
      | r2_hidden('#skF_3'(A_209),u1_pre_topc(A_209))
      | v2_pre_topc(A_209)
      | ~ r2_hidden(u1_struct_0(A_209),u1_pre_topc(A_209))
      | ~ l1_pre_topc(A_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4823,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0('#skF_5'),'#skF_1'('#skF_5')),u1_pre_topc('#skF_4'))
    | r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_5'))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_391,c_4810])).

tff(c_4833,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0('#skF_4'),'#skF_1'('#skF_5')),u1_pre_topc('#skF_4'))
    | r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_4'))
    | v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_495,c_218,c_391,c_391,c_218,c_4823])).

tff(c_4834,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0('#skF_4'),'#skF_1'('#skF_5')),u1_pre_topc('#skF_4'))
    | r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_4833])).

tff(c_4838,plain,(
    ~ r2_hidden(k5_setfam_1(u1_struct_0('#skF_4'),'#skF_1'('#skF_5')),u1_pre_topc('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_4834])).

tff(c_4841,plain,
    ( ~ r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_4'))
    | ~ m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_4838])).

tff(c_4845,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_58,c_4536,c_508,c_4841])).

tff(c_4847,plain,(
    r2_hidden(k5_setfam_1(u1_struct_0('#skF_4'),'#skF_1'('#skF_5')),u1_pre_topc('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_4834])).

tff(c_5118,plain,(
    ! [A_222] :
      ( ~ r2_hidden(k5_setfam_1(u1_struct_0(A_222),'#skF_1'(A_222)),u1_pre_topc(A_222))
      | r2_hidden('#skF_2'(A_222),u1_pre_topc(A_222))
      | v2_pre_topc(A_222)
      | ~ r2_hidden(u1_struct_0(A_222),u1_pre_topc(A_222))
      | ~ l1_pre_topc(A_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_5138,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0('#skF_5'),'#skF_1'('#skF_5')),u1_pre_topc('#skF_4'))
    | r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_5'))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_391,c_5118])).

tff(c_5153,plain,
    ( r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_4'))
    | v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_495,c_218,c_391,c_391,c_4847,c_218,c_5138])).

tff(c_5155,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_4537,c_5153])).

tff(c_5157,plain,(
    ~ r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_494])).

tff(c_473,plain,(
    ! [A_68] :
      ( r1_tarski('#skF_1'(A_68),u1_pre_topc(A_68))
      | m1_subset_1('#skF_2'(A_68),k1_zfmisc_1(u1_struct_0(A_68)))
      | v2_pre_topc(A_68)
      | ~ r2_hidden(u1_struct_0(A_68),u1_pre_topc(A_68))
      | ~ l1_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_478,plain,
    ( r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_5'))
    | m1_subset_1('#skF_2'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_473])).

tff(c_481,plain,
    ( r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_4'))
    | m1_subset_1('#skF_2'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_391,c_218,c_391,c_478])).

tff(c_482,plain,
    ( r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_4'))
    | m1_subset_1('#skF_2'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ r2_hidden(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_481])).

tff(c_5548,plain,
    ( r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_4'))
    | m1_subset_1('#skF_2'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_495,c_482])).

tff(c_5549,plain,(
    m1_subset_1('#skF_2'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_5157,c_5548])).

tff(c_5156,plain,(
    r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_494])).

tff(c_5212,plain,(
    ! [A_227] :
      ( r1_tarski('#skF_1'(A_227),u1_pre_topc(A_227))
      | m1_subset_1('#skF_3'(A_227),k1_zfmisc_1(u1_struct_0(A_227)))
      | v2_pre_topc(A_227)
      | ~ r2_hidden(u1_struct_0(A_227),u1_pre_topc(A_227))
      | ~ l1_pre_topc(A_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_5217,plain,
    ( r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_5'))
    | m1_subset_1('#skF_3'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_5212])).

tff(c_5220,plain,
    ( r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_4'))
    | m1_subset_1('#skF_3'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_495,c_218,c_391,c_391,c_5217])).

tff(c_5221,plain,(
    m1_subset_1('#skF_3'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_5157,c_5220])).

tff(c_12,plain,(
    ! [A_2] :
      ( r1_tarski('#skF_1'(A_2),u1_pre_topc(A_2))
      | r2_hidden('#skF_3'(A_2),u1_pre_topc(A_2))
      | v2_pre_topc(A_2)
      | ~ r2_hidden(u1_struct_0(A_2),u1_pre_topc(A_2))
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_412,plain,
    ( r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_5'))
    | r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_5'))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_4'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_391,c_12])).

tff(c_440,plain,
    ( r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_4'))
    | r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_4'))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_218,c_391,c_391,c_412])).

tff(c_441,plain,
    ( r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_4'))
    | r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_4'))
    | ~ r2_hidden(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_440])).

tff(c_5172,plain,
    ( r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_4'))
    | r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_495,c_441])).

tff(c_5173,plain,(
    r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_5157,c_5172])).

tff(c_5224,plain,(
    ! [B_27] : k9_subset_1(u1_struct_0('#skF_4'),B_27,'#skF_3'('#skF_5')) = k3_xboole_0(B_27,'#skF_3'('#skF_5')) ),
    inference(resolution,[status(thm)],[c_5221,c_54])).

tff(c_7692,plain,(
    ! [A_301,B_302,C_303] :
      ( r2_hidden(k9_subset_1(u1_struct_0(A_301),B_302,C_303),u1_pre_topc(A_301))
      | ~ r2_hidden(C_303,u1_pre_topc(A_301))
      | ~ r2_hidden(B_302,u1_pre_topc(A_301))
      | ~ m1_subset_1(C_303,k1_zfmisc_1(u1_struct_0(A_301)))
      | ~ m1_subset_1(B_302,k1_zfmisc_1(u1_struct_0(A_301)))
      | ~ v2_pre_topc(A_301)
      | ~ l1_pre_topc(A_301) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_7725,plain,(
    ! [B_27] :
      ( r2_hidden(k3_xboole_0(B_27,'#skF_3'('#skF_5')),u1_pre_topc('#skF_4'))
      | ~ r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_4'))
      | ~ r2_hidden(B_27,u1_pre_topc('#skF_4'))
      | ~ m1_subset_1('#skF_3'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_pre_topc('#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5224,c_7692])).

tff(c_7751,plain,(
    ! [B_305] :
      ( r2_hidden(k3_xboole_0(B_305,'#skF_3'('#skF_5')),u1_pre_topc('#skF_4'))
      | ~ r2_hidden(B_305,u1_pre_topc('#skF_4'))
      | ~ m1_subset_1(B_305,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_58,c_5221,c_5173,c_7725])).

tff(c_6757,plain,(
    ! [A_278] :
      ( r1_tarski('#skF_1'(A_278),u1_pre_topc(A_278))
      | ~ r2_hidden(k9_subset_1(u1_struct_0(A_278),'#skF_2'(A_278),'#skF_3'(A_278)),u1_pre_topc(A_278))
      | v2_pre_topc(A_278)
      | ~ r2_hidden(u1_struct_0(A_278),u1_pre_topc(A_278))
      | ~ l1_pre_topc(A_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6772,plain,
    ( r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ r2_hidden(k9_subset_1(u1_struct_0('#skF_5'),'#skF_2'('#skF_5'),'#skF_3'('#skF_5')),u1_pre_topc('#skF_4'))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_391,c_6757])).

tff(c_6781,plain,
    ( r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_4'))
    | ~ r2_hidden(k3_xboole_0('#skF_2'('#skF_5'),'#skF_3'('#skF_5')),u1_pre_topc('#skF_4'))
    | v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_495,c_218,c_391,c_5224,c_218,c_391,c_6772])).

tff(c_6782,plain,(
    ~ r2_hidden(k3_xboole_0('#skF_2'('#skF_5'),'#skF_3'('#skF_5')),u1_pre_topc('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_5157,c_6781])).

tff(c_7754,plain,
    ( ~ r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_4'))
    | ~ m1_subset_1('#skF_2'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_7751,c_6782])).

tff(c_7758,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5549,c_5156,c_7754])).

%------------------------------------------------------------------------------
