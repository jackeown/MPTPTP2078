%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:02 EST 2020

% Result     : Theorem 3.29s
% Output     : CNFRefutation 3.63s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 183 expanded)
%              Number of leaves         :   35 (  87 expanded)
%              Depth                    :   11
%              Number of atoms          :  262 (1294 expanded)
%              Number of equality atoms :    5 (  61 expanded)
%              Maximal formula depth    :   25 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tmap_1,type,(
    r1_tmap_1: ( $i * $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_210,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(B),u1_struct_0(A))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,B) )
                   => ! [E] :
                        ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(B)))
                       => ! [F] :
                            ( m1_subset_1(F,u1_struct_0(B))
                           => ! [G] :
                                ( m1_subset_1(G,u1_struct_0(D))
                               => ( ( v3_pre_topc(E,B)
                                    & r2_hidden(F,E)
                                    & r1_tarski(E,u1_struct_0(D))
                                    & F = G )
                                 => ( r1_tmap_1(B,A,C,F)
                                  <=> r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),G) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tmap_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_73,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m1_connsp_2(C,A,B)
              <=> r2_hidden(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).

tff(f_160,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(B),u1_struct_0(A))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,B) )
                 => ! [E] :
                      ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(B)))
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(B))
                         => ! [G] :
                              ( m1_subset_1(G,u1_struct_0(D))
                             => ( ( r1_tarski(E,u1_struct_0(D))
                                  & m1_connsp_2(E,B,F)
                                  & F = G )
                               => ( r1_tmap_1(B,A,C,F)
                                <=> r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),G) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tmap_1)).

tff(f_113,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(B),u1_struct_0(A))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,B) )
                 => ! [E] :
                      ( m1_subset_1(E,u1_struct_0(B))
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(D))
                         => ( ( E = F
                              & r1_tmap_1(B,A,C,E) )
                           => r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),F) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tmap_1)).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_40,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_36,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_26,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_34,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_71,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_34])).

tff(c_28,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_52,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_50,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_32,plain,(
    v3_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_189,plain,(
    ! [B_353,A_354,C_355] :
      ( r1_tarski(B_353,k1_tops_1(A_354,C_355))
      | ~ r1_tarski(B_353,C_355)
      | ~ v3_pre_topc(B_353,A_354)
      | ~ m1_subset_1(C_355,k1_zfmisc_1(u1_struct_0(A_354)))
      | ~ m1_subset_1(B_353,k1_zfmisc_1(u1_struct_0(A_354)))
      | ~ l1_pre_topc(A_354) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_194,plain,(
    ! [B_353] :
      ( r1_tarski(B_353,k1_tops_1('#skF_2','#skF_5'))
      | ~ r1_tarski(B_353,'#skF_5')
      | ~ v3_pre_topc(B_353,'#skF_2')
      | ~ m1_subset_1(B_353,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_38,c_189])).

tff(c_199,plain,(
    ! [B_356] :
      ( r1_tarski(B_356,k1_tops_1('#skF_2','#skF_5'))
      | ~ r1_tarski(B_356,'#skF_5')
      | ~ v3_pre_topc(B_356,'#skF_2')
      | ~ m1_subset_1(B_356,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_194])).

tff(c_206,plain,
    ( r1_tarski('#skF_5',k1_tops_1('#skF_2','#skF_5'))
    | ~ r1_tarski('#skF_5','#skF_5')
    | ~ v3_pre_topc('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_199])).

tff(c_210,plain,(
    r1_tarski('#skF_5',k1_tops_1('#skF_2','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_6,c_206])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_30,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_109,plain,(
    ! [C_340,A_341,B_342] :
      ( r2_hidden(C_340,A_341)
      | ~ r2_hidden(C_340,B_342)
      | ~ m1_subset_1(B_342,k1_zfmisc_1(A_341)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_113,plain,(
    ! [A_343] :
      ( r2_hidden('#skF_6',A_343)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_343)) ) ),
    inference(resolution,[status(thm)],[c_30,c_109])).

tff(c_127,plain,(
    ! [B_344] :
      ( r2_hidden('#skF_6',B_344)
      | ~ r1_tarski('#skF_5',B_344) ) ),
    inference(resolution,[status(thm)],[c_12,c_113])).

tff(c_8,plain,(
    ! [C_6,A_3,B_4] :
      ( r2_hidden(C_6,A_3)
      | ~ r2_hidden(C_6,B_4)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_146,plain,(
    ! [A_347,B_348] :
      ( r2_hidden('#skF_6',A_347)
      | ~ m1_subset_1(B_348,k1_zfmisc_1(A_347))
      | ~ r1_tarski('#skF_5',B_348) ) ),
    inference(resolution,[status(thm)],[c_127,c_8])).

tff(c_157,plain,(
    ! [B_8,A_7] :
      ( r2_hidden('#skF_6',B_8)
      | ~ r1_tarski('#skF_5',A_7)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(resolution,[status(thm)],[c_12,c_146])).

tff(c_217,plain,(
    ! [B_357] :
      ( r2_hidden('#skF_6',B_357)
      | ~ r1_tarski(k1_tops_1('#skF_2','#skF_5'),B_357) ) ),
    inference(resolution,[status(thm)],[c_210,c_157])).

tff(c_222,plain,(
    r2_hidden('#skF_6',k1_tops_1('#skF_2','#skF_5')) ),
    inference(resolution,[status(thm)],[c_6,c_217])).

tff(c_338,plain,(
    ! [C_374,A_375,B_376] :
      ( m1_connsp_2(C_374,A_375,B_376)
      | ~ r2_hidden(B_376,k1_tops_1(A_375,C_374))
      | ~ m1_subset_1(C_374,k1_zfmisc_1(u1_struct_0(A_375)))
      | ~ m1_subset_1(B_376,u1_struct_0(A_375))
      | ~ l1_pre_topc(A_375)
      | ~ v2_pre_topc(A_375)
      | v2_struct_0(A_375) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_344,plain,
    ( m1_connsp_2('#skF_5','#skF_2','#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_222,c_338])).

tff(c_358,plain,
    ( m1_connsp_2('#skF_5','#skF_2','#skF_6')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_36,c_38,c_344])).

tff(c_359,plain,(
    m1_connsp_2('#skF_5','#skF_2','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_358])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_62,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_7')
    | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_70,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6')
    | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_62])).

tff(c_126,plain,(
    ~ r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_58,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_56,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_48,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_46,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_68,plain,
    ( r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
    | r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_69,plain,
    ( r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
    | r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_68])).

tff(c_138,plain,(
    r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_126,c_69])).

tff(c_532,plain,(
    ! [C_397,A_396,G_401,E_398,B_399,D_400] :
      ( r1_tmap_1(B_399,A_396,C_397,G_401)
      | ~ r1_tmap_1(D_400,A_396,k2_tmap_1(B_399,A_396,C_397,D_400),G_401)
      | ~ m1_connsp_2(E_398,B_399,G_401)
      | ~ r1_tarski(E_398,u1_struct_0(D_400))
      | ~ m1_subset_1(G_401,u1_struct_0(D_400))
      | ~ m1_subset_1(G_401,u1_struct_0(B_399))
      | ~ m1_subset_1(E_398,k1_zfmisc_1(u1_struct_0(B_399)))
      | ~ m1_pre_topc(D_400,B_399)
      | v2_struct_0(D_400)
      | ~ m1_subset_1(C_397,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_399),u1_struct_0(A_396))))
      | ~ v1_funct_2(C_397,u1_struct_0(B_399),u1_struct_0(A_396))
      | ~ v1_funct_1(C_397)
      | ~ l1_pre_topc(B_399)
      | ~ v2_pre_topc(B_399)
      | v2_struct_0(B_399)
      | ~ l1_pre_topc(A_396)
      | ~ v2_pre_topc(A_396)
      | v2_struct_0(A_396) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_536,plain,(
    ! [E_398] :
      ( r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
      | ~ m1_connsp_2(E_398,'#skF_2','#skF_6')
      | ~ r1_tarski(E_398,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(E_398,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_pre_topc('#skF_4','#skF_2')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))))
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_138,c_532])).

tff(c_543,plain,(
    ! [E_398] :
      ( r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
      | ~ m1_connsp_2(E_398,'#skF_2','#skF_6')
      | ~ r1_tarski(E_398,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_398,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_50,c_48,c_46,c_44,c_40,c_36,c_71,c_536])).

tff(c_545,plain,(
    ! [E_402] :
      ( ~ m1_connsp_2(E_402,'#skF_2','#skF_6')
      | ~ r1_tarski(E_402,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_402,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_42,c_126,c_543])).

tff(c_555,plain,
    ( ~ m1_connsp_2('#skF_5','#skF_2','#skF_6')
    | ~ r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_38,c_545])).

tff(c_563,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_359,c_555])).

tff(c_565,plain,(
    r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_806,plain,(
    ! [B_439,F_438,A_441,D_442,C_440] :
      ( r1_tmap_1(D_442,A_441,k2_tmap_1(B_439,A_441,C_440,D_442),F_438)
      | ~ r1_tmap_1(B_439,A_441,C_440,F_438)
      | ~ m1_subset_1(F_438,u1_struct_0(D_442))
      | ~ m1_subset_1(F_438,u1_struct_0(B_439))
      | ~ m1_pre_topc(D_442,B_439)
      | v2_struct_0(D_442)
      | ~ m1_subset_1(C_440,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_439),u1_struct_0(A_441))))
      | ~ v1_funct_2(C_440,u1_struct_0(B_439),u1_struct_0(A_441))
      | ~ v1_funct_1(C_440)
      | ~ l1_pre_topc(B_439)
      | ~ v2_pre_topc(B_439)
      | v2_struct_0(B_439)
      | ~ l1_pre_topc(A_441)
      | ~ v2_pre_topc(A_441)
      | v2_struct_0(A_441) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_808,plain,(
    ! [D_442,F_438] :
      ( r1_tmap_1(D_442,'#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3',D_442),F_438)
      | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3',F_438)
      | ~ m1_subset_1(F_438,u1_struct_0(D_442))
      | ~ m1_subset_1(F_438,u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_442,'#skF_2')
      | v2_struct_0(D_442)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_44,c_806])).

tff(c_814,plain,(
    ! [D_442,F_438] :
      ( r1_tmap_1(D_442,'#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3',D_442),F_438)
      | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3',F_438)
      | ~ m1_subset_1(F_438,u1_struct_0(D_442))
      | ~ m1_subset_1(F_438,u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_442,'#skF_2')
      | v2_struct_0(D_442)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_50,c_48,c_46,c_808])).

tff(c_898,plain,(
    ! [D_451,F_452] :
      ( r1_tmap_1(D_451,'#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3',D_451),F_452)
      | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3',F_452)
      | ~ m1_subset_1(F_452,u1_struct_0(D_451))
      | ~ m1_subset_1(F_452,u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_451,'#skF_2')
      | v2_struct_0(D_451) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_814])).

tff(c_564,plain,(
    ~ r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_903,plain,
    ( ~ r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_898,c_564])).

tff(c_910,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_71,c_565,c_903])).

tff(c_912,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_910])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:48:56 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.29/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.63/1.54  
% 3.63/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.63/1.54  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.63/1.54  
% 3.63/1.54  %Foreground sorts:
% 3.63/1.54  
% 3.63/1.54  
% 3.63/1.54  %Background operators:
% 3.63/1.54  
% 3.63/1.54  
% 3.63/1.54  %Foreground operators:
% 3.63/1.54  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.63/1.54  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.63/1.54  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.63/1.54  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.63/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.63/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.63/1.54  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.63/1.54  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.63/1.54  tff('#skF_7', type, '#skF_7': $i).
% 3.63/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.63/1.54  tff('#skF_5', type, '#skF_5': $i).
% 3.63/1.54  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.63/1.54  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.63/1.54  tff('#skF_6', type, '#skF_6': $i).
% 3.63/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.63/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.63/1.54  tff('#skF_1', type, '#skF_1': $i).
% 3.63/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.63/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.63/1.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.63/1.54  tff('#skF_4', type, '#skF_4': $i).
% 3.63/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.63/1.54  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.63/1.54  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.63/1.54  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.63/1.54  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.63/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.63/1.54  
% 3.63/1.56  tff(f_210, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((v3_pre_topc(E, B) & r2_hidden(F, E)) & r1_tarski(E, u1_struct_0(D))) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_tmap_1)).
% 3.63/1.56  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.63/1.56  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 3.63/1.56  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.63/1.56  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 3.63/1.56  tff(f_73, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 3.63/1.56  tff(f_160, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (((r1_tarski(E, u1_struct_0(D)) & m1_connsp_2(E, B, F)) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tmap_1)).
% 3.63/1.56  tff(f_113, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tmap_1)).
% 3.63/1.56  tff(c_42, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.63/1.56  tff(c_40, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.63/1.56  tff(c_36, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.63/1.56  tff(c_26, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.63/1.56  tff(c_34, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.63/1.56  tff(c_71, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_34])).
% 3.63/1.56  tff(c_28, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.63/1.56  tff(c_54, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.63/1.56  tff(c_52, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.63/1.56  tff(c_50, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.63/1.56  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.63/1.56  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.63/1.56  tff(c_32, plain, (v3_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.63/1.56  tff(c_189, plain, (![B_353, A_354, C_355]: (r1_tarski(B_353, k1_tops_1(A_354, C_355)) | ~r1_tarski(B_353, C_355) | ~v3_pre_topc(B_353, A_354) | ~m1_subset_1(C_355, k1_zfmisc_1(u1_struct_0(A_354))) | ~m1_subset_1(B_353, k1_zfmisc_1(u1_struct_0(A_354))) | ~l1_pre_topc(A_354))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.63/1.56  tff(c_194, plain, (![B_353]: (r1_tarski(B_353, k1_tops_1('#skF_2', '#skF_5')) | ~r1_tarski(B_353, '#skF_5') | ~v3_pre_topc(B_353, '#skF_2') | ~m1_subset_1(B_353, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_189])).
% 3.63/1.56  tff(c_199, plain, (![B_356]: (r1_tarski(B_356, k1_tops_1('#skF_2', '#skF_5')) | ~r1_tarski(B_356, '#skF_5') | ~v3_pre_topc(B_356, '#skF_2') | ~m1_subset_1(B_356, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_194])).
% 3.63/1.56  tff(c_206, plain, (r1_tarski('#skF_5', k1_tops_1('#skF_2', '#skF_5')) | ~r1_tarski('#skF_5', '#skF_5') | ~v3_pre_topc('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_199])).
% 3.63/1.56  tff(c_210, plain, (r1_tarski('#skF_5', k1_tops_1('#skF_2', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_6, c_206])).
% 3.63/1.56  tff(c_12, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.63/1.56  tff(c_30, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.63/1.56  tff(c_109, plain, (![C_340, A_341, B_342]: (r2_hidden(C_340, A_341) | ~r2_hidden(C_340, B_342) | ~m1_subset_1(B_342, k1_zfmisc_1(A_341)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.63/1.56  tff(c_113, plain, (![A_343]: (r2_hidden('#skF_6', A_343) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_343)))), inference(resolution, [status(thm)], [c_30, c_109])).
% 3.63/1.56  tff(c_127, plain, (![B_344]: (r2_hidden('#skF_6', B_344) | ~r1_tarski('#skF_5', B_344))), inference(resolution, [status(thm)], [c_12, c_113])).
% 3.63/1.56  tff(c_8, plain, (![C_6, A_3, B_4]: (r2_hidden(C_6, A_3) | ~r2_hidden(C_6, B_4) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.63/1.56  tff(c_146, plain, (![A_347, B_348]: (r2_hidden('#skF_6', A_347) | ~m1_subset_1(B_348, k1_zfmisc_1(A_347)) | ~r1_tarski('#skF_5', B_348))), inference(resolution, [status(thm)], [c_127, c_8])).
% 3.63/1.56  tff(c_157, plain, (![B_8, A_7]: (r2_hidden('#skF_6', B_8) | ~r1_tarski('#skF_5', A_7) | ~r1_tarski(A_7, B_8))), inference(resolution, [status(thm)], [c_12, c_146])).
% 3.63/1.56  tff(c_217, plain, (![B_357]: (r2_hidden('#skF_6', B_357) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_5'), B_357))), inference(resolution, [status(thm)], [c_210, c_157])).
% 3.63/1.56  tff(c_222, plain, (r2_hidden('#skF_6', k1_tops_1('#skF_2', '#skF_5'))), inference(resolution, [status(thm)], [c_6, c_217])).
% 3.63/1.56  tff(c_338, plain, (![C_374, A_375, B_376]: (m1_connsp_2(C_374, A_375, B_376) | ~r2_hidden(B_376, k1_tops_1(A_375, C_374)) | ~m1_subset_1(C_374, k1_zfmisc_1(u1_struct_0(A_375))) | ~m1_subset_1(B_376, u1_struct_0(A_375)) | ~l1_pre_topc(A_375) | ~v2_pre_topc(A_375) | v2_struct_0(A_375))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.63/1.56  tff(c_344, plain, (m1_connsp_2('#skF_5', '#skF_2', '#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_222, c_338])).
% 3.63/1.56  tff(c_358, plain, (m1_connsp_2('#skF_5', '#skF_2', '#skF_6') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_36, c_38, c_344])).
% 3.63/1.56  tff(c_359, plain, (m1_connsp_2('#skF_5', '#skF_2', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_54, c_358])).
% 3.63/1.56  tff(c_60, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.63/1.56  tff(c_62, plain, (~r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_7') | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.63/1.56  tff(c_70, plain, (~r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6') | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_62])).
% 3.63/1.56  tff(c_126, plain, (~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6')), inference(splitLeft, [status(thm)], [c_70])).
% 3.63/1.56  tff(c_58, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.63/1.56  tff(c_56, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.63/1.56  tff(c_48, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.63/1.56  tff(c_46, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.63/1.56  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.63/1.56  tff(c_68, plain, (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6') | r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.63/1.56  tff(c_69, plain, (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6') | r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_68])).
% 3.63/1.56  tff(c_138, plain, (r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_126, c_69])).
% 3.63/1.56  tff(c_532, plain, (![C_397, A_396, G_401, E_398, B_399, D_400]: (r1_tmap_1(B_399, A_396, C_397, G_401) | ~r1_tmap_1(D_400, A_396, k2_tmap_1(B_399, A_396, C_397, D_400), G_401) | ~m1_connsp_2(E_398, B_399, G_401) | ~r1_tarski(E_398, u1_struct_0(D_400)) | ~m1_subset_1(G_401, u1_struct_0(D_400)) | ~m1_subset_1(G_401, u1_struct_0(B_399)) | ~m1_subset_1(E_398, k1_zfmisc_1(u1_struct_0(B_399))) | ~m1_pre_topc(D_400, B_399) | v2_struct_0(D_400) | ~m1_subset_1(C_397, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_399), u1_struct_0(A_396)))) | ~v1_funct_2(C_397, u1_struct_0(B_399), u1_struct_0(A_396)) | ~v1_funct_1(C_397) | ~l1_pre_topc(B_399) | ~v2_pre_topc(B_399) | v2_struct_0(B_399) | ~l1_pre_topc(A_396) | ~v2_pre_topc(A_396) | v2_struct_0(A_396))), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.63/1.56  tff(c_536, plain, (![E_398]: (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6') | ~m1_connsp_2(E_398, '#skF_2', '#skF_6') | ~r1_tarski(E_398, u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_2')) | ~m1_subset_1(E_398, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_138, c_532])).
% 3.63/1.56  tff(c_543, plain, (![E_398]: (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6') | ~m1_connsp_2(E_398, '#skF_2', '#skF_6') | ~r1_tarski(E_398, u1_struct_0('#skF_4')) | ~m1_subset_1(E_398, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_50, c_48, c_46, c_44, c_40, c_36, c_71, c_536])).
% 3.63/1.56  tff(c_545, plain, (![E_402]: (~m1_connsp_2(E_402, '#skF_2', '#skF_6') | ~r1_tarski(E_402, u1_struct_0('#skF_4')) | ~m1_subset_1(E_402, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_42, c_126, c_543])).
% 3.63/1.56  tff(c_555, plain, (~m1_connsp_2('#skF_5', '#skF_2', '#skF_6') | ~r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_38, c_545])).
% 3.63/1.56  tff(c_563, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_359, c_555])).
% 3.63/1.56  tff(c_565, plain, (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6')), inference(splitRight, [status(thm)], [c_70])).
% 3.63/1.56  tff(c_806, plain, (![B_439, F_438, A_441, D_442, C_440]: (r1_tmap_1(D_442, A_441, k2_tmap_1(B_439, A_441, C_440, D_442), F_438) | ~r1_tmap_1(B_439, A_441, C_440, F_438) | ~m1_subset_1(F_438, u1_struct_0(D_442)) | ~m1_subset_1(F_438, u1_struct_0(B_439)) | ~m1_pre_topc(D_442, B_439) | v2_struct_0(D_442) | ~m1_subset_1(C_440, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_439), u1_struct_0(A_441)))) | ~v1_funct_2(C_440, u1_struct_0(B_439), u1_struct_0(A_441)) | ~v1_funct_1(C_440) | ~l1_pre_topc(B_439) | ~v2_pre_topc(B_439) | v2_struct_0(B_439) | ~l1_pre_topc(A_441) | ~v2_pre_topc(A_441) | v2_struct_0(A_441))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.63/1.56  tff(c_808, plain, (![D_442, F_438]: (r1_tmap_1(D_442, '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', D_442), F_438) | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', F_438) | ~m1_subset_1(F_438, u1_struct_0(D_442)) | ~m1_subset_1(F_438, u1_struct_0('#skF_2')) | ~m1_pre_topc(D_442, '#skF_2') | v2_struct_0(D_442) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_806])).
% 3.63/1.56  tff(c_814, plain, (![D_442, F_438]: (r1_tmap_1(D_442, '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', D_442), F_438) | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', F_438) | ~m1_subset_1(F_438, u1_struct_0(D_442)) | ~m1_subset_1(F_438, u1_struct_0('#skF_2')) | ~m1_pre_topc(D_442, '#skF_2') | v2_struct_0(D_442) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_50, c_48, c_46, c_808])).
% 3.63/1.56  tff(c_898, plain, (![D_451, F_452]: (r1_tmap_1(D_451, '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', D_451), F_452) | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', F_452) | ~m1_subset_1(F_452, u1_struct_0(D_451)) | ~m1_subset_1(F_452, u1_struct_0('#skF_2')) | ~m1_pre_topc(D_451, '#skF_2') | v2_struct_0(D_451))), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_814])).
% 3.63/1.56  tff(c_564, plain, (~r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6')), inference(splitRight, [status(thm)], [c_70])).
% 3.63/1.56  tff(c_903, plain, (~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_898, c_564])).
% 3.63/1.56  tff(c_910, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_71, c_565, c_903])).
% 3.63/1.56  tff(c_912, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_910])).
% 3.63/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.63/1.56  
% 3.63/1.56  Inference rules
% 3.63/1.56  ----------------------
% 3.63/1.56  #Ref     : 0
% 3.63/1.56  #Sup     : 160
% 3.63/1.56  #Fact    : 0
% 3.63/1.56  #Define  : 0
% 3.63/1.56  #Split   : 16
% 3.63/1.56  #Chain   : 0
% 3.63/1.56  #Close   : 0
% 3.63/1.56  
% 3.63/1.56  Ordering : KBO
% 3.63/1.56  
% 3.63/1.56  Simplification rules
% 3.63/1.56  ----------------------
% 3.63/1.56  #Subsume      : 32
% 3.63/1.56  #Demod        : 157
% 3.63/1.56  #Tautology    : 33
% 3.63/1.56  #SimpNegUnit  : 21
% 3.63/1.56  #BackRed      : 0
% 3.63/1.56  
% 3.63/1.56  #Partial instantiations: 0
% 3.63/1.56  #Strategies tried      : 1
% 3.63/1.56  
% 3.63/1.56  Timing (in seconds)
% 3.63/1.56  ----------------------
% 3.63/1.56  Preprocessing        : 0.37
% 3.63/1.56  Parsing              : 0.19
% 3.63/1.56  CNF conversion       : 0.05
% 3.63/1.56  Main loop            : 0.43
% 3.63/1.56  Inferencing          : 0.15
% 3.63/1.56  Reduction            : 0.14
% 3.63/1.56  Demodulation         : 0.10
% 3.63/1.56  BG Simplification    : 0.02
% 3.63/1.56  Subsumption          : 0.09
% 3.63/1.56  Abstraction          : 0.02
% 3.63/1.56  MUC search           : 0.00
% 3.63/1.56  Cooper               : 0.00
% 3.63/1.56  Total                : 0.83
% 3.63/1.56  Index Insertion      : 0.00
% 3.63/1.56  Index Deletion       : 0.00
% 3.63/1.56  Index Matching       : 0.00
% 3.63/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
